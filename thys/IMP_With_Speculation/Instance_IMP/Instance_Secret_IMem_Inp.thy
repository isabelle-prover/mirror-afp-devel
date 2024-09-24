section \<open>Relative Security Instance: Secret Memory Input\<close>

text \<open> This theory sets up an instance of Relative Security used to prove an Security of a potentially infinite program\<close>

theory Instance_Secret_IMem_Inp
  imports Instance_Common "Relative_Security.Relative_Security"
begin                                                                            

text "Using the following notation to denote an undefined element"
no_notation bot (\<open>\<bottom>\<close>)

definition ffile :: "vname" where "ffile = ''ffile''"
definition xx :: "vname" where "xx = ''x''"
definition yy :: "vname" where "yy = ''yy''"  
type_synonym secret = "state \<times> val \<times> val"

abbreviation writeSecretOnFile where "writeSecretOnFile \<equiv> (Output T (Fun (V xx) (V yy)))"
lemma writeOnFile_not_Jump[simp]:"\<not>is_IfJump writeSecretOnFile" by (simp add: )
lemma writeOnFile_not_Inp[simp]:"\<not>is_getInput writeSecretOnFile" by (simp add: )
lemma writeOnFile_not_Fence[simp]:"writeSecretOnFile \<noteq> Fence" by (simp add: )

definition ffileVal where "ffileVal cfg = vstoreOf(cfg) ffile"
lemma ffileVal_vstore[simp]:"ffileVal cfg = vstoreOf(cfg) ffile" by(simp add: ffileVal_def)


context Prog_Mispred
begin

text "The following functions and definitions make up the required components of the Relative Security locale"
fun corrState :: "stateV \<Rightarrow> stateO \<Rightarrow> bool" where 
"corrState cfgO cfgA = True"

(* All our programs will have "Start" followed by the rest, with the rest not containing "Start". 
The secret will be "uploaded" at this Start moment. *)
definition isSecV :: "stateV \<Rightarrow> bool" where 
"isSecV ss \<equiv> case ss of (cfg,ibT,ibUT,ls) \<Rightarrow> \<not>finalN ss"
(* We consider the entire initial state as a secret: *)
fun getSecV :: "stateV \<Rightarrow> secret" where 
"getSecV (cfg,ibT,ibUT,ls) = 
 (case prog!(pcOf cfg) of 
    Start \<Rightarrow> (stateOf cfg, \<bottom>, \<bottom>)
   |Input T _ \<Rightarrow> (\<bottom>, lhd ibT, \<bottom>)
   |Output T _ \<Rightarrow> (\<bottom>,\<bottom>,outOf (prog!(pcOf cfg)) (stateOf cfg))
   |_ \<Rightarrow> (\<bottom>,\<bottom>,\<bottom>))"


lemma isSecV_iff:"isSecV ss \<longleftrightarrow> \<not>finalN ss" 
  unfolding isSecV_def 
  by (simp add: case_prod_beta)

(* The secrecy infrastructure is similar to that of the "original" semantics: *)
definition isSecO :: "stateO \<Rightarrow> bool" where 
"isSecO ss \<equiv> case ss of (pstate,cfg,cfgs,ibT,ibUT,ls) \<Rightarrow> \<not>finalS ss \<and> cfgs = []"
fun getSecO :: "stateO \<Rightarrow> secret" where 
"getSecO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (case prog!(pcOf cfg) of 
    Start \<Rightarrow> (stateOf cfg, \<bottom>, \<bottom>)
   |Input T _ \<Rightarrow> (\<bottom>, lhd ibT, \<bottom>)
   |Output T _ \<Rightarrow> (\<bottom>,\<bottom>,outOf (prog!(pcOf cfg)) (stateOf cfg))
   |_ \<Rightarrow> (\<bottom>,\<bottom>,\<bottom>))"
end (* context Prog_Mispred *)




sublocale Prog_Mispred_Init < Rel_Sec where 
  validTransV = validTransV and istateV = istateV  
  and finalV = finalN
  and isSecV = isSecV and getSecV = getSecV
  and isIntV = isIntV and getIntV = getIntV  
  (* *)
  and validTransO = validTransO and istateO = istateO
  and finalO = finalS
  and isSecO = isSecO  and getSecO = getSecO
  and isIntO = isIntO and getIntO = getIntO 
  and corrState = corrState 
  apply standard 
  subgoal by (simp add: finalN_defs)
  subgoal for s by (cases s, simp)
  subgoal by(simp add:isSecV_def) 
  subgoal by (simp add: finalS_defs)
  subgoal by (simp add: finalS_defs)  
  subgoal for ss apply(cases ss) subgoal for ps cfg cfgs ib ls apply(cases cfg) subgoal for n s 
  unfolding isSecO_def finalS_def final_def
  using stepS_0[of ps s ib ls] by auto . . .


(* *)


context Prog_Mispred_Init 
begin

lemmas reachV_induct = Van.reach.induct[split_format(complete)]
lemmas reachO_induct = Opt.reach.induct[split_format(complete)]

lemma is_getInputT_getActV[simp]: 
"(prog!(pcOf cfg)) = Input U inp \<Longrightarrow> getActV (cfg,ibT,ibUT,ls) = lhd ibUT"
  by (cases "prog!(pcOf cfg)", auto simp: Van.getAct_def)

lemma is_getInputU_getActV[simp]: 
"(prog!(pcOf cfg)) = Input T inp \<Longrightarrow> getActV (cfg,ibT,ibUT,ls) = lhd ibT"
by (cases "prog!(pcOf cfg)", auto simp: Van.getAct_def)

lemma not_is_getInput_getActV[simp]: 
"\<not> is_getInput (prog!(pcOf cfg)) \<Longrightarrow> getActV (cfg,ibT,ibUT,ls) = \<bottom>"
apply (cases "prog!(pcOf cfg)", auto simp: Van.getAct_def)
  subgoal for t apply(cases t, simp_all) . .

lemma is_Output_getObsV[simp]: 
"(prog!(pcOf cfg)) = Output U out \<Longrightarrow> getObsV (cfg,ibT,ibUT,ls) = 
 (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)"
by (cases "prog!(pcOf cfg)", auto simp: Van.getObs_def)

lemma not_is_Output_getObsV[simp]: 
"\<not> is_Output (prog!(pcOf cfg)) \<Longrightarrow> getObsV (cfg,ibT,ibUT,ls) = \<bottom>"
apply (cases "prog!(pcOf cfg)", auto simp: Van.getObs_def)
  subgoal for t apply(cases t, simp_all) . .
(* *)

lemma is_getInputT_Nil_getActO[simp]: 
"(prog!(pcOf cfg)) = Input T inp  \<Longrightarrow> getActO (pstate,cfg,[],ibT,ibUT,ls) = lhd ibT"
  by (cases "prog!(pcOf cfg)", auto simp: Opt.getAct_def)

lemma is_getInputU_Nil_getActO[simp]: 
"(prog!(pcOf cfg)) = Input U inp \<Longrightarrow> getActO (pstate,cfg,[],ibT,ibUT,ls) = lhd ibUT"
by (cases "prog!(pcOf cfg)", auto simp: Opt.getAct_def)

lemma not_is_getInput_Nil_getActO[simp]: 
"(\<not> is_getInput (prog!(pcOf cfg))) 
\<or> cfgs \<noteq> [] \<Longrightarrow> getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = \<bottom>"
apply (cases cfgs, auto)
   apply (cases "prog!(pcOf cfg)", auto simp: Opt.getAct_def)
  subgoal for t apply(cases t, simp_all) . .

lemma is_Output_Nil_getObsO[simp]: 
"(prog!(pcOf cfg)) = Output U out \<Longrightarrow> 
 getObsO (pstate,cfg,[],ibT,ibUT,ls) = (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)"
by (cases "prog!(pcOf cfg)", auto simp: Opt.getObs_def)

lemma not_is_Output_Nil_getObsO[simp]: 
"\<not> is_Output (prog!(pcOf cfg)) \<or> cfgs \<noteq> [] \<Longrightarrow> getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = \<bottom>"
apply (cases cfgs, auto)
apply (cases "prog!(pcOf cfg)", auto simp: Opt.getObs_def)
  subgoal for t apply(cases t, simp_all) . .

(* *)



lemma getActV_simps: 
"getActV (cfg,ibT,ibUT,ls) = 
 (case prog!(pcOf cfg) of 
    Input T _   \<Rightarrow> lhd ibT
   |Input U _ \<Rightarrow> lhd ibUT
   |_ \<Rightarrow> \<bottom> 
 )"
  unfolding Van.getAct_def 
  apply (simp split: com.splits, safe)
  subgoal for t apply(cases t, simp_all) . 
  subgoal for t apply(cases t, simp_all) . .

lemma getObsV_simps: 
"getObsV (cfg,ibT,ibUT,ls) = 
 (case prog!(pcOf cfg) of 
    Output U _ \<Rightarrow> (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
   |_ \<Rightarrow> \<bottom> 
 )"
  unfolding Van.getObs_def
  apply (simp split: com.splits, safe)
  subgoal for t apply(cases t, simp_all) . 
  subgoal for t apply(cases t, simp_all) . .

lemma getActO_simps: 
"getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (case (cfgs,prog!(pcOf cfg)) of 
    ([],Input T _)   \<Rightarrow> lhd ibT
   |([],Input U _) \<Rightarrow> lhd ibUT
   |_ \<Rightarrow> \<bottom> 
 )"
  unfolding Van.getAct_def
  apply (simp split: com.splits list.splits, safe)
  subgoal for t apply(cases t, simp_all) . .

lemma getObsO_simps: 
"getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (case (cfgs,prog!(pcOf cfg)) of 
    ([],Output U _) \<Rightarrow> (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
   |_ \<Rightarrow> \<bottom> 
 )"
  unfolding Opt.getObs_def
  apply (simp split: com.splits list.splits, safe)
  subgoal for t apply(cases t, simp_all) . 
  subgoal for t apply(cases t, simp_all) . .


end (* context Prog_Mispred_Init *)


end 
