section \<open>Relative Security Instance: Secret Memory\<close>

text \<open> This theory sets up an instance of Relative Security with the secrets as the initial memories\<close>

theory Instance_Secret_IMem
imports Instance_Common "Relative_Security.Relative_Security"
begin

no_notation bot (\<open>\<bottom>\<close>)
type_synonym secret = "state"

context Prog_Mispred
begin 

fun corrState :: "stateV \<Rightarrow> stateO \<Rightarrow> bool" where 
"corrState cfgO cfgA = True"


text \<open>Since all our programs will have "Start" followed by the rest, with the rest not containing "Start". 
The secret will be "uploaded" at this Start moment.\<close>
definition isSecV :: "stateV \<Rightarrow> bool" where 
"isSecV ss \<equiv> case ss of (cfg,ibT,ibUT) \<Rightarrow> (pcOf cfg = 0)"
text \<open>We consider the entire initial state as a secret:\<close>
fun getSecV :: "stateV \<Rightarrow> secret" where 
"getSecV (cfg,ibT,ibUT) = stateOf cfg"

text \<open>The secrecy infrastructure is similar to that of the "original" semantics:\<close>
definition isSecO :: "stateO \<Rightarrow> bool" where 
"isSecO ss \<equiv> case ss of (pstate,cfg,cfgs,ibT,ibUT,ls) \<Rightarrow> (pcOf cfg = 0 \<and> cfgs = [])"
fun getSecO :: "stateO \<Rightarrow> secret" where 
"getSecO (pstate,cfg,cfgs,ibT,ibUT,ls) = stateOf cfg"
lemma isSecV_iff:"isSecV ss \<longleftrightarrow> pcOf (fst ss) = 0" 
  unfolding isSecV_def 
  by (simp add: case_prod_beta)

lemma validTransO_iff_nextS: "validTransO (s1,    s2) = (\<not> finalS s1 \<and> (stepS s1 s2))"
  unfolding finalS_def final_def 
by simp (metis old.prod.exhaust)

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
  subgoal for s apply(cases s) subgoal for cfg ibT ibUT ls apply(cases cfg) subgoal for n st 
  unfolding isSecV_def  
  using stebB_0[of st ibT ibUT] stepB_iff_nextB by fastforce . .
  subgoal by (simp add: finalS_defs)
  subgoal by (simp add: finalS_defs)  
  subgoal for ss apply(cases ss) subgoal for ps cfg cfgs ibT ibUT ls apply(cases cfg) subgoal for n st 
  unfolding isSecO_def finalS_def final_def
  using stepS_0[of ps st ibT ibUT ls] by auto . . .


(* *)


context Prog_Mispred_Init 
begin

lemmas reachV_induct = Van.reach.induct[split_format(complete)]
lemmas reachO_induct = Opt.reach.induct[split_format(complete)]

lemma is_getTrustedInput_getActV[simp]: 
"(prog!(pcOf cfg)) = Input T s \<Longrightarrow> getActV (cfg,ibT,ibUT,ls) = lhd ibT"
by (cases "prog!(pcOf cfg)", auto simp: Van.getAct_def)

lemma not_is_getTrustedInput_getActV[simp]: 
"\<not> is_getInput (prog!(pcOf cfg)) \<Longrightarrow> getActV (cfg,ibT,ibUT,ls) = noninform"
apply (cases "prog!(pcOf cfg)", auto simp: Van.getAct_def )
  subgoal for x by (cases x, simp_all) . 

lemma is_Output_getObsV[simp]: 
"(prog!(pcOf cfg)) = Output U out \<Longrightarrow> getObsV (cfg,ibT,ibUT,ls) = 
 (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)"
by (cases "prog!(pcOf cfg)", auto simp: Van.getObs_def)

lemma not_is_Output_getObsV[simp]: 
"\<not> is_Output (prog!(pcOf cfg)) \<Longrightarrow> getObsV (cfg,ibT,ibUT,ls) = \<bottom>"
apply (cases "prog!(pcOf cfg)", auto simp: Van.getObs_def)
  subgoal for x by (cases x, simp_all) . 
(* *)

lemma is_getTrustedInput_Nil_getActO[simp]: 
"(prog!(pcOf cfg)) = Input T s \<Longrightarrow> getActO (pstate,cfg,[],ibT,ibUT,ls) = lhd ibT"
by (cases "prog!(pcOf cfg)", auto simp: Opt.getAct_def)

lemma not_is_getTrustedInput_Nil_getActO[simp]: 
"\<not> is_getInput (prog!(pcOf cfg))
 \<or> cfgs \<noteq> [] \<Longrightarrow> getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = \<bottom>"
apply (cases cfgs, auto)
apply (cases "prog!(pcOf cfg)", auto simp: Opt.getAct_def)
  subgoal for x by (cases x, simp_all) . 

lemma is_Output_Nil_getObsO[simp]: 
"prog!(pcOf cfg) = Output U s \<Longrightarrow> 
 getObsO (pstate,cfg,[],ibT,ibUT,ls) = (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)"
  by (cases "prog!(pcOf cfg)", auto simp: Opt.getObs_def)

lemma not_is_Output_Nil_getObsO[simp]: 
"\<not> is_Output (prog!(pcOf cfg)) \<or> cfgs \<noteq> [] \<Longrightarrow> getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = \<bottom>"
apply (cases cfgs, auto)
apply (cases "prog!(pcOf cfg)", auto simp: Opt.getObs_def)
  subgoal for x by (cases x, simp_all) . 
(* *)

lemma getActV_simps: 
"getActV (cfg,ibT,ibUT,ls) = 
 (case prog!(pcOf cfg) of 
    Input T _ \<Rightarrow> lhd ibT
   |Input U _ \<Rightarrow> lhd ibUT
   |_ \<Rightarrow> \<bottom> 
 )"
  unfolding Van.getAct_def 
  apply (simp split: com.splits, safe)
  subgoal for t by(cases t, simp_all)
  subgoal for t by(cases t, simp_all) .

lemma getObsV_simps: 
"getObsV (cfg,ibT,ibUT,ls) = 
 (case prog!(pcOf cfg) of 
    Output U _ \<Rightarrow> (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
   |_ \<Rightarrow> \<bottom> 
 )"
unfolding Van.getObs_def 
  apply (simp split: com.splits, safe)
  subgoal for t by(cases t, simp_all) 
  subgoal for t by(cases t, simp_all) .

lemma getActO_simps: 
"getActO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (case (cfgs,prog!(pcOf cfg)) of 
    ([],Input T _) \<Rightarrow> lhd ibT
   |([],Input U _) \<Rightarrow> lhd ibUT
   |_ \<Rightarrow> \<bottom> 
 )"
  apply (simp split: com.splits list.splits, safe)
  unfolding Opt.getAct_def 
  subgoal for t by(cases t, simp_all) .

lemma getObsO_simps: 
"getObsO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (case (cfgs,prog!(pcOf cfg)) of 
    ([],Output U _) \<Rightarrow> (outOf (prog!(pcOf cfg)) (stateOf cfg), ls)
   |_ \<Rightarrow> \<bottom> 
 )"
  unfolding Opt.getObs_def
  apply (simp split: com.splits list.splits, safe)  
  subgoal for t by(cases t, simp_all) 
  subgoal for t by(cases t, simp_all) .


end (* context Prog_Mispred_Init *)


end 
