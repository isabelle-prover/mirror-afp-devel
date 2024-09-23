section "Proof of Relative Security for fun4"
theory Fun4
  imports "../Instance_IMP/Instance_Secret_IMem"
  "Relative_Security.Unwinding_fin"
begin 

subsection "Function definition and Boilerplate"
no_notation bot (\<open>\<bottom>\<close>)

consts NN :: nat
consts size_aa1 :: nat
consts size_aa2 :: nat
lemma NN: "int NN \<ge> 0" by auto

locale array_nempty = assumes aa1:"size_aa1 > 0" and NN: "int NN > 0"

definition aa1 :: "avname" where "aa1 = ''a1''" 
definition aa2 :: "avname" where "aa2 = ''a2''" 
definition vv :: "avname" where "vv = ''v''" 
definition xx :: "avname" where "xx = ''i''" 
definition tt :: "avname" where "tt = ''w''" 


lemmas vvars_defs = aa1_def aa2_def vv_def xx_def tt_def

lemma vvars_dff[simp]: 
  "aa1 \<noteq> aa2" "aa1 \<noteq> vv" "aa1 \<noteq> xx" "aa1 \<noteq> tt"
  "aa2 \<noteq> aa1" "aa2 \<noteq> vv" "aa2 \<noteq> xx" "aa1 \<noteq> tt"
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
 \<^cancel>\<open>3 \<close> IfJump (Less (V xx) (N NN)) 4 6 ,
 \<^cancel>\<open>4 \<close>   vv ::= VA aa1 (N 0) ,
 \<^cancel>\<open>5 \<close>   tt ::= Plus (VA aa2 (Times (V vv) (N 512))) (V xx) ,
 \<^cancel>\<open>6 \<close> Output U (V tt) 
]"

(* *)

lemma cases_6: "(i::pcounter) = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 \<or> 
 i = 6 \<or> i > 6"
  apply(cases i, simp_all) 
  subgoal for i apply(cases i, simp_all)
  subgoal for i apply(cases i, simp_all)
  subgoal for i apply(cases i, simp_all)
  subgoal for i apply(cases i, simp_all)
  subgoal for i apply(cases i, simp_all)
  subgoal for i apply(cases i, simp_all)
                  . . . . . . . 


lemma cases_thenBranch: "(i::pcounter) < 4 \<or> i = 4 \<or> i = 5 \<or> i = 6 \<or> i > 6"
  apply(cases i, simp_all) 
  subgoal for i apply(cases i, simp_all)
    subgoal for i apply(cases i, simp_all)
      subgoal for i apply(cases i, simp_all)
        subgoal for i apply(cases i, simp_all)
          subgoal for i apply(cases i, simp_all)
          subgoal for i apply(cases i, simp_all)
            . . . . . . .




lemma xx_NN_cases: "vs xx < int NN \<or> vs xx \<ge> int NN" by auto

lemma is_If_pcOf[simp]: 
  "pcOf cfg < 7 \<Longrightarrow> is_IfJump (prog ! (pcOf cfg)) \<longleftrightarrow> pcOf cfg = 3"
  apply(cases cfg) subgoal for pc s using cases_6[of "pcOf cfg"] 
    by (auto simp: prog_def) .

lemma is_If_pc[simp]: 
  "pc < 7 \<Longrightarrow> is_IfJump (prog ! pc) \<longleftrightarrow> pc = 3"
  using cases_6[of pc] 
  by (auto simp: prog_def) 

lemma is_If_pcThen[simp]: "pcOf cfg \<in> {4..6} \<Longrightarrow> \<not>is_IfJump (prog ! pcOf cfg)" 
  using cases_thenBranch[of "pcOf cfg"] 
  by (auto simp: prog_def) 


(* *)

consts mispred :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool"
fun resolve :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool" where
  "resolve p pc = (if (pc = [6,6] \<or> pc = [4,6]) then True else False)"

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
  stepB_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix \<open>\<rightarrow>B\<close> 55)
  where "x \<rightarrow>B y == stepB x y"

abbreviation
  stepsB_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix \<open>\<rightarrow>B*\<close> 55)
  where "x \<rightarrow>B* y == star stepB x y"

abbreviation
  stepM_abbrev :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix \<open>\<rightarrow>M\<close> 55)
  where "x \<rightarrow>M y == stepM x y"

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

lemma endPC[simp]: "endPC = 7"
  unfolding endPC_def unfolding prog_def by auto

(* *)

lemma is_getUntrustedInput_pcOf[simp]: "pcOf cfg < 7 \<Longrightarrow> is_getInput (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 1"
  using cases_6[of "pcOf cfg"] by (auto simp: prog_def)

lemma getUntrustedInput_pcOf[simp]: " prog!1 = Input U xx"
  by (auto simp: prog_def)

lemma is_getTrustedInput[simp]: "is_getInput (prog ! 1)"
  unfolding prog_def by auto

lemma getInput_not4[simp]:"\<not>is_getInput (prog ! 4)"
  unfolding prog_def by auto
lemma getInput_not5[simp]:"\<not>is_getInput (prog ! 5)"
  unfolding prog_def by auto
lemma OutputT_not6[simp]:"(prog ! 6) = Output U (V tt)"
  unfolding prog_def by auto

lemma is_Output_pcOf[simp]: "pcOf cfg < 7 \<Longrightarrow> is_Output (prog!(pcOf cfg)) \<longleftrightarrow> pcOf cfg = 6"
  using cases_6[of "pcOf cfg"] by (auto simp: prog_def)


lemma is_Fence_pcOf[simp]:"pcOf cfg < 7 \<Longrightarrow>  prog ! (pcOf cfg) \<noteq> Fence" 
  using cases_6[of "pcOf cfg"] by (auto simp: prog_def)

lemma is_Fence_pcThen[simp]: "3 \<le> pcOf cfg \<and> pcOf cfg \<le> 5 \<Longrightarrow> (prog ! pcOf cfg)\<noteq>Fence" 
  using cases_thenBranch[of "pcOf cfg"] 
  by (auto simp: prog_def) 

lemma is_Output[simp]: "is_Output (prog ! 6)"
  unfolding is_Output_def prog_def by auto

lemma getInput_not[intro]:"is_getInput (prog ! 4) \<Longrightarrow> False" unfolding prog_def by simp
lemma Output_not4[intro]:"is_Output (prog ! 4) \<Longrightarrow> False" unfolding prog_def by simp
lemma Fence_not4[intro]:"prog ! 4 = Fence \<Longrightarrow> False" unfolding prog_def by simp

lemma getInput_not55[intro]:"is_getInput (prog ! 5) \<Longrightarrow> False" unfolding prog_def by simp
lemma Output_not5[intro]:"is_Output (prog ! 5) \<Longrightarrow> False" unfolding prog_def by simp
lemma Fence_not5[intro]:"prog ! 5 = Fence \<Longrightarrow> False" unfolding prog_def by simp
(* *)
lemma Jump_not6:"\<not> is_IfJump (prog ! 6)"unfolding prog_def by simp

lemma isSecV_pcOf[simp]: 
  "isSecV (cfg,ibT,ibUT) \<longleftrightarrow> pcOf cfg = 0"
  using isSecV_def by simp

lemma isSecO_pcOf[simp]: 
  "isSecO (pstate,cfg,cfgs,ibT,ibUT,ls) \<longleftrightarrow> (pcOf cfg = 0 \<and> cfgs = [])"
  using isSecO_def by simp

(* *)

lemma inputT_not[simp]: "pcOf cfg < 7 \<Longrightarrow> 
(prog ! pcOf cfg) \<noteq> Input T inp"
apply(cases cfg) subgoal for pc s using cases_6[of "pcOf cfg "] 
by (auto simp: prog_def) .

lemma getActV_pcOf[simp]: 
  "pcOf cfg < 7 \<Longrightarrow> 
 getActV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 1 then lhd ibUT else \<bottom>)"
  apply(subst getActV_simps) unfolding prog_def 
  apply simp  
  using getActV_simps not_is_getTrustedInput_getActV prog_def by auto

lemma getObsV_pcOf[simp]: 
  "pcOf cfg < 7 \<Longrightarrow>  
 getObsV (cfg,ibT,ibUT,ls) = 
 (if pcOf cfg = 6 then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
  apply(subst getObsV_simps) 
  unfolding prog_def apply simp  
  using getObsV_simps not_is_Output_getObsV is_Output_pcOf prog_def 
  by (auto,simp)

lemma getObsV_pcOf6[simp]: 
  "pcOf cfg = 6 \<Longrightarrow>  
 getObsV (cfg,ibT,ibUT,ls) = 
 (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
" 
  by simp


lemma getActO_pcOf[simp]: 
  "pcOf cfg < 7 \<Longrightarrow> 
 getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if pcOf cfg = 1 \<and> cfgs = [] then lhd ibUT else \<bottom>)"
  apply(subst getActO_simps)
  apply(cases cfgs, auto)
  unfolding prog_def apply simp 
  using getActV_simps getActV_pcOf prog_def by presburger

lemma getObsO_pcOf[simp]: 
  "pcOf cfg < 7 \<Longrightarrow>  
 getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (if (pcOf cfg = 6 \<and> cfgs = []) then 
  (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
  else \<bottom> 
 )"
  apply(subst getObsO_simps) 
  apply(cases cfgs, auto)
  unfolding prog_def
  using getObsV_simps is_Output_pcOf not_is_Output_getObsV prog_def by presburger 

(* *)

lemma eqSec_pcOf[simp]: 
  "eqSec (cfg1, ibT, ibUT1, ls1) (pstate3, cfg3, cfgs3, ibT3, ibUT3, ls3) \<longleftrightarrow> 
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
"ibUT \<noteq> LNil \<Longrightarrow> nextB (Config 1 (State (Vstore vs) avst h p), ibT, ibUT) = 
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
 (Config 6 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextB_IfFalse)
unfolding endPC_def unfolding prog_def by auto

lemma nextB_pc3: 
"nextB (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config (if vs xx < int NN then 4 else 6) (State (Vstore vs) avst h p), ibT, ibUT)"
  by(cases "vs xx < int NN", auto)

lemma nextM_pc3_then[simp]: 
"vs xx \<ge> int NN \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 4 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextM_IfTrue)
unfolding endPC_def unfolding prog_def by auto

lemma nextM_pc3_else[simp]: 
"vs xx < int NN \<Longrightarrow>
 nextM (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config 6 (State (Vstore vs) avst h p), ibT, ibUT)"
apply(subst nextM_IfFalse)
unfolding endPC_def unfolding prog_def by auto

lemma nextM_pc3: 
"nextM (Config 3 (State (Vstore vs) avst h p), ibT, ibUT) = 
 (Config (if vs xx < int NN then 6 else 4) (State (Vstore vs) avst h p), ibT, ibUT)"
by(cases "vs xx < int NN", auto)

lemma readLocs_pc3[simp]: 
"readLocs (Config 3 s) = {}"
unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc4[simp]: 
  "nextB (Config 4 (State (Vstore vs) avst (Heap h) p), ibT,ibUT) = 
 (let l = array_loc aa1 0 avst 
  in (Config 5 (State (Vstore (vs(vv := h l))) avst (Heap h) p)), ibT,ibUT)"
  apply(subst nextB_Assign)
  unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc4[simp]: 
  "readLocs (Config 4 (State (Vstore vs) avst h p)) = {array_loc aa1 0 avst}"
  unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc5[simp]: 
  "nextB (Config 5 (State (Vstore vs) avst (Heap h) p), ibT,ibUT) = 
 (let l = array_loc aa2 (nat (vs vv * 512)) avst
  in (Config 6 (State (Vstore (vs(tt := h l + vs xx))) avst (Heap h) p)), ibT,ibUT)"
  apply(subst nextB_Assign)
  unfolding endPC_def unfolding prog_def by auto 

lemma readLocs_pc5[simp]: 
  "readLocs (Config 5 (State (Vstore vs) avst h p)) = {array_loc aa2 (nat (vs vv * 512)) avst}"
  unfolding endPC_def readLocs_def unfolding prog_def by auto

(* *)

lemma nextB_pc6[simp]: 
  "nextB (Config 6 s, ibT,ibUT) = (Config 7 s, ibT,ibUT)"
  apply(subst nextB_Output)
  unfolding endPC_def unfolding prog_def by auto

lemma readLocs_pc6[simp]: 
  "readLocs (Config 6 (State (Vstore vs) avst h p)) = {}"
  unfolding endPC_def readLocs_def unfolding prog_def by auto


(**)

lemma nextB_stepB_pc: 
  "pc < 7 \<Longrightarrow> (pc = 1 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> 
(Config pc s, ibT,ibUT) \<rightarrow>B nextB (Config pc s, ibT,ibUT)"
  apply(cases s) subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
    subgoal for vs as h
      using cases_6[of pc] apply safe
      subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
        by (simp add: prog_def)
      subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
        by (simp add: prog_def)
          (* *)
      subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
        by (simp add: prog_def, metis llist.collapse)
      subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
        by (simp add: prog_def)      subgoal apply simp apply(subst stepB.simps) unfolding endPC_def 
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
      subgoal by auto
      subgoal by auto 
      . . . 
(**)
lemma nextB_avst_consistent_aux: 
  "4 \<le> pc \<and> pc \<le> 6 \<Longrightarrow>
   (nextB (Config pc (State (Vstore vs) avst (Heap h) p),ibT,ibUT)) = (Config pc' (State (Vstore vs') avst' (Heap h') p'),ibT,ibUT') \<Longrightarrow> 
    avst = avst' \<and> 
    vs xx = vs' xx \<and>
    h = h'"
  using cases_thenBranch[of pc] 
  apply safe
           apply simp_all by auto  


lemma nextB_avst_consistent: 
  "4 \<le> pcOf cfg \<and> pcOf cfg \<le> 6 \<Longrightarrow>
   (nextB (cfg, ibT,ibUT)) = (cfg', ibT,ibUT') \<Longrightarrow> 
    (getAvstore (stateOf cfg)) = (getAvstore (stateOf cfg')) \<and> 
    (getHheap (stateOf cfg)) = (getHheap (stateOf cfg')) \<and> 
    vstore (getVstore (stateOf cfg)) xx = vstore (getVstore (stateOf cfg')) xx"
  apply(cases cfg) subgoal for pc s 
    apply(cases s) subgoal for vstore avst heap_h p 
      apply (cases heap_h, cases vstore, cases avst) subgoal for h vs 
        apply(cases cfg') subgoal for pc' s'
          apply(cases s') subgoal for vstore' avst' heap_h' p' 
            apply (cases heap_h', cases vstore', cases avst')  subgoal for h vs 
              using nextB_avst_consistent_aux apply simp
              by blast . . . . . .


lemma nextB_pcs_consistent: 
  "4 \<le> pcOf cfg1 \<and> pcOf cfg1 \<le> 6 \<Longrightarrow> pcOf cfg1 = pcOf cfg2 \<Longrightarrow> 
   (nextB (cfg1, ibT1, ibUT1)) = (cfg1', ibT1', ibUT1') \<Longrightarrow> 
   (nextB (cfg2, ibT2, ibUT2)) = (cfg2', ibT2', ibUT2') \<Longrightarrow>
    pcOf cfg1' = pcOf cfg2'"
  apply (cases cfg1, cases cfg2, cases cfg1', cases cfg2')
  subgoal for pc1 s1 pc2 s2 pc1' s1' pc2' s2'
  apply(cases s1, cases s2, cases s1', cases s2')
  subgoal for vs1 avst1 h1 p1 vs2 avst2 h2 p2
              vs1' avst1' h1' p1' vs2' avst2' h2' p2'
  apply(cases vs1, cases vs2, cases h1, cases h2)
  using cases_6[of "pcOf cfg1"] apply safe
  by simp_all  . . 


lemma not_finalB: 
  "pc < 7 \<Longrightarrow> (pc = 1 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> 
 \<not> finalB (Config pc s, ibT, ibUT)"
  using nextB_stepB_pc by (simp add: stepB_iff_nextB)

lemma finalB_pc_iff': 
  "pc < 7 \<Longrightarrow>
 finalB (Config pc s, ibT, ibUT) \<longleftrightarrow> 
 (pc = 1 \<and> ibUT = LNil)"
  subgoal apply safe
    subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
    subgoal using nextB_stepB_pc[of pc] by (auto simp add: stepB_iff_nextB) 
    subgoal using finalB_iff getUntrustedInput_pcOf by auto . .

lemma finalB_pc_iff: 
"pc \<le> 7 \<Longrightarrow>
 finalB (Config pc s, ibT, ibUT) \<longleftrightarrow> 
 (pc = 1 \<and> ibUT = LNil \<or> pc = 7)"
  using cases_6[of pc] apply (elim disjE, simp add: finalB_def)
  subgoal by (meson final_def stebB_0)
  by (simp add: finalB_pc_iff' finalB_endPC)+

lemma finalB_pcOf_iff[simp]:
  "pcOf cfg \<le> 7 \<Longrightarrow> 
 finalB (cfg, ibT, ibUT) \<longleftrightarrow> (pcOf cfg = 1 \<and> ibUT = LNil \<or> pcOf cfg = 7)"
  by (metis config.exhaust config.sel(1) finalB_pc_iff)


lemma finalS_cond:"pcOf cfg < 7 \<Longrightarrow> cfgs = [] \<Longrightarrow> (pcOf cfg = 1 \<longrightarrow> ibUT \<noteq> LNil) \<Longrightarrow> \<not> finalS (pstate, cfg, cfgs, ibT,ibUT, ls)"
  apply(cases cfg)
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
    subgoal for vs as h
      using cases_6[of pc] apply(elim disjE) unfolding finalS_defs
      subgoal using nonspec_normal[of "[]" "Config pc (State (Vstore vs) avst hh p)" 
                                        pstate pstate ibT ibUT 
                                        "Config 1 (State (Vstore vs) avst hh p)" 
                                        ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls]
        using is_If_pc by force


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
      subgoal apply(frule nonspec_mispred[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                             pstate "update pstate [pcOf (Config pc (State (Vstore vs) avst hh p))]"
                                             ibT ibUT "Config (if vs xx < NN then 4 else 6) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "Config (if vs xx < NN then 6 else 4) (State (Vstore vs) avst hh p)"
                                             ibT ibUT "[Config (if vs xx < NN then 6 else 4) (State (Vstore vs) avst hh p)]"
                                             "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 9 subgoal by metis by (simp add: finalM_iff)+

      subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)"
                                    pstate pstate ibT ibUT 
                                    "Config (if vs xx < NN then 4 else 6) (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
      prefer 7 subgoal by metis by simp_all . 

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                         pstate pstate ibT ibUT 
                         "(let l = (array_loc aa1 0 avst) 
                           in (Config 5 (State (Vstore (vs(vv := h l))) avst hh p)))" 
                         ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                         pstate pstate ibT ibUT 
                         "(let l = (array_loc aa2 (nat (vs vv * 512)) avst) 
                                in (Config 6 (State (Vstore (vs(tt := h l + vs xx))) avst hh p)))" 
                         ibT ibUT "[]" "ls \<union> readLocs (Config pc (State (Vstore vs) avst hh p))" ls])
            prefer 7 subgoal by metis by simp_all

    subgoal apply(frule nonspec_normal[of cfgs "Config pc (State (Vstore vs) avst hh p)" 
                                    pstate pstate ibT ibUT 
                                    "Config 7 (State (Vstore vs) avst hh p)" 
                                    ibT ibUT "[]" ls ls])
            prefer 7 subgoal by metis by simp_all
    by simp_all . . .


lemma finalS_cond_spec:
      "pcOf cfg < 7 \<Longrightarrow> 
       ((pcOf (last cfgs) = 4 \<or> pcOf (last cfgs) = 5 \<or> pcOf (last cfgs) = 6) \<and> pcOf cfg = 6) \<or> (pcOf (last cfgs) = 6 \<and> pcOf cfg = 4) \<Longrightarrow> 
       length cfgs =  Suc 0 \<Longrightarrow>
      \<not> finalS (pstate, cfg, cfgs, ibT,ibUT, ls)"
  apply(cases cfg)
  subgoal for pc s apply(cases s)
  subgoal for vst avst hh p apply(cases vst, cases avst, cases hh)
  subgoal for vs as h apply(cases "last cfgs")
  subgoal for pcs ss apply(cases ss)
  subgoal for vsts avsts hhs ps apply(cases vsts, cases avsts, cases hhs, simp)
    subgoal for vss ass hs apply(elim disjE, elim conjE, elim disjE, simp) 
      unfolding finalS_defs
      subgoal apply(rule notI,
            erule allE[of _ "(pstate,Config 6 (State (Vstore vs) (Avstore as) (Heap h) p),
                            [Config 5 (State (Vstore (vss(vv := hs (array_loc aa1 (nat 0) avsts)))) avsts hhs ps)],
                            ibT,ibUT,ls \<union> readLocs (last cfgs))"], erule notE, 
                            rule spec_normal[of _ _ _ _ _ _"Config 5 (State (Vstore (vss(vv := hs (array_loc aa1 (nat 0) avsts)))) avsts hhs ps)"])
        by auto
      subgoal apply(rule notI, 
            erule allE[of _ "(pstate,Config 6 (State (Vstore vs) (Avstore as) (Heap h) p),
                            [Config 6 (State (Vstore (vss(tt := hs (array_loc aa2 (nat (vss vv * 512)) avsts) + vss xx))) avsts hhs ps)],
                            ibT,ibUT,ls \<union> readLocs (last cfgs))"], erule notE, 
                            rule spec_normal[of _ _ _ _ _ _"Config 6 (State (Vstore (vss(tt := hs (array_loc aa2 (nat (vss vv * 512)) avsts) + vss xx))) avsts hhs ps)"])

        prefer 7 apply auto[1]
        by auto

      subgoal apply(rule notI, 
      erule allE[of _ "(update pstate (6 # map pcOf cfgs),Config 6 (State (Vstore vs) (Avstore as) (Heap h) p),
                       [],ibT,ibUT,ls)"]) 
      by(erule notE, rule spec_resolve, auto)

      subgoal apply(rule notI, 
      erule allE[of _ "(update pstate (4 # map pcOf cfgs),Config 4 (State (Vstore vs) (Avstore as) (Heap h) p),
                       [],ibT,ibUT,ls)"])
      by(erule notE, rule spec_resolve, auto) . . . . . . . 

end