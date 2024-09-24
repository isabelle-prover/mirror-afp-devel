section "Misprediction and Speculative Semantics"

text \<open>This theory formalizes an optimized speculative semantics, which allows for a characterization of the Spectre vulnerability, this work is inspired and based off the speculative semantics introduced by Cheang et al. \cite{Cheang}\<close>

theory Step_Spec
imports Step_Basic
begin

subsection "Misprediction Oracle"
text \<open>The speculative semantics is parameterised by a misprediction oracle. 
This consists of a predictor state:\<close>
typedecl predState

text \<open>Along with predicates "mispred" (which decides when a misprediction occurs), "resolve" (which decides for when a speculation is resolved)\<close>
text \<open>Both depend on the predictor state (which evolves via the update function) and the program counters of nested speculation\<close>
locale Prog_Mispred = 
Prog prog 
for prog :: "com list"
+ 
fixes mispred :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool"
and resolve :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool"
and update :: "predState \<Rightarrow> pcounter list \<Rightarrow> predState"
begin 

subsection "Mispredicting Step"
text "stepM simply goes the other way than stepB at branches"
inductive
stepM :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist \<Rightarrow> bool" (infix \<open>\<rightarrow>M\<close> 55)
where
IfTrue[intro]: 
"pc < endPC \<Longrightarrow> prog!pc = IfJump b pc1 pc2 \<Longrightarrow> 
 bval b s \<Longrightarrow> 
 (Config pc s, ibT, ibUT) \<rightarrow>M (Config pc2 s, ibT, ibUT)" 
|
IfFalse[intro]: 
"pc < endPC \<Longrightarrow> prog!pc = IfJump b pc1 pc2 \<Longrightarrow> 
 \<not> bval b s \<Longrightarrow> 
 (Config pc s, ibT, ibUT) \<rightarrow>M (Config pc1 s, ibT, ibUT)"

subsubsection "State Transitions"
definition "finalM = final stepM"

lemma finalM_iff_aux:  
"pc < endPC \<and> is_IfJump (prog!pc) 
 \<longleftrightarrow> 
 (\<exists>cfg'. (Config pc s, ibT, ibUT) \<rightarrow>M cfg')"
apply (cases s) subgoal for vst avst h p apply clarsimp  (* apply clarsimp subgoal for vs hh  *)
(* apply safe subgoal *)
apply (cases "prog!pc")
  subgoal by (auto elim: stepM.cases)
  subgoal by (auto elim: stepM.cases)
  subgoal by (auto elim: stepM.cases)  
  subgoal by (auto elim: stepM.cases)
  subgoal by (auto elim: stepM.cases)
  subgoal by (auto elim: stepM.cases) 
  subgoal by (auto elim: stepM.cases) 
  subgoal by (auto elim: stepM.cases) 
  subgoal by (auto elim: stepM.cases) 
  subgoal by (auto elim: stepM.cases,meson IfFalse IfTrue) . .

lemma finalM_iff: 
"finalM (Config pc (State vst avst h p), ibT, ibUT) 
 \<longleftrightarrow>
 (pc \<ge> endPC \<or> \<not> is_IfJump (prog!pc))"
using finalM_iff_aux unfolding finalM_def final_def  
by (metis linorder_not_less)

lemma finalB_imp_finalM: 
"finalB (cfg, ibT, ibUT) \<Longrightarrow> finalM (cfg, ibT, ibUT)"
apply(cases cfg) subgoal for pc s apply(cases s)
subgoal for vst avst h p apply clarsimp unfolding finalB_iff finalM_iff by auto . .

lemma not_finalM_imp_not_finalB: 
"\<not> finalM (cfg, ibT, ibUT) \<Longrightarrow> \<not> finalB (cfg, ibT, ibUT)"
using finalB_imp_finalM by blast

(* *)

lemma stepM_determ:
"cfg_ib \<rightarrow>M cfg_ib' \<Longrightarrow> cfg_ib \<rightarrow>M cfg_ib'' \<Longrightarrow> cfg_ib'' = cfg_ib'"
apply(induction arbitrary: cfg_ib'' rule: stepM.induct)
by (auto elim: stepM.cases)
 
definition nextM :: "config \<times> val llist \<times> val llist \<Rightarrow> config \<times> val llist \<times> val llist" where 
"nextM cfg_ib \<equiv> SOME cfg'_ib'. cfg_ib \<rightarrow>M cfg'_ib'"
 
lemma nextM_stepM: "\<not> finalM cfg_ib \<Longrightarrow> cfg_ib \<rightarrow>M (nextM cfg_ib)"
unfolding nextM_def apply(rule someI_ex) 
unfolding finalM_def final_def by auto

lemma stepM_nextM: "cfg_ib \<rightarrow>M cfg'_ib' \<Longrightarrow> cfg'_ib' = nextM cfg_ib"
unfolding nextM_def apply(rule sym) apply(rule some_equality)
using stepM_determ by auto

lemma nextM_iff_stepM: "\<not> finalM cfg_ib \<Longrightarrow> nextM cfg_ib  = cfg'_ib' \<longleftrightarrow> cfg_ib \<rightarrow>M cfg'_ib'"
using nextM_stepM stepM_nextM by blast

lemma stepM_iff_nextM: "cfg_ib \<rightarrow>M cfg'_ib' \<longleftrightarrow> \<not> finalM cfg_ib \<and> nextM cfg_ib  = cfg'_ib'"
by (metis finalM_def final_def stepM_nextM)

(* *)

lemma nextM_IfTrue[simp]:  
"pc < endPC \<Longrightarrow> prog!pc = IfJump b pc1 pc2 \<Longrightarrow> 
 \<not> bval b s \<Longrightarrow> 
 nextM (Config pc s, ibT, ibUT) = (Config pc1 s, ibT, ibUT)" 
by(intro stepM_nextM[THEN sym] stepM.intros)

lemma nextM_IfFalse[simp]:  
"pc < endPC \<Longrightarrow> prog!pc = IfJump b pc1 pc2 \<Longrightarrow> 
 bval b s \<Longrightarrow> 
 nextM (Config pc s, ibT, ibUT) = (Config pc2 s, ibT, ibUT)" 
by(intro stepM_nextM[THEN sym] stepM.intros)

end (* context Prog_Mispred *)

subsection "Speculative Semantics"
text \<open>A "speculative" configuration is a quadruple consisting of:
\begin{itemize}
\item The predictor's state
\item The nonspeculative configuration (at level 0 so to speak)
\item The list of speculative configurations (modelling nested speculation, levels 1 to n, from left to right: so the last in this list is at the current speculaton level, n)
\item The list of inputs in the input buffer
\end{itemize}
\<close>

text \<open>We think of cfgs as a stack of configurations, one for each speculation level in a nested speculative execution. 
At level 0 (empty list) we have the configuration for normal, non-speculative execution. 
At each moment, only the top of the configuration stack, "hd cfgs" is active.\<close>

type_synonym configS = "predState \<times> config \<times> config list \<times> val llist \<times> val llist \<times> loc set"

context Prog_Mispred
begin

text \<open>The speculative semantics is more involved than both the normal and basic semantics, so a short description of each rule is provided:
\begin{itemize}
\item Non\_spec\_ normal: when we are either not mispredicting or not at a branch and there is no current speculation, i.e. normal execution

\item Nonspec\_mispred: when we are mispredicting and at a branch, speculation occurs down the wrong branch, i.e. branch misprediction

\item Spec\_normal: when we are either not mispredicting or not at a branch BUT there is speculation, i.e. standard speculative execution

\item Spec\_mispred: when we are mispredicting and at a branch, AND also speculating... speculation occurs down the wrong branch, and we go to another speculation level i.e. nested speculative execution

\item Spec\_Fence: when there is current speculation and a Fence is hit, all speculation resolves

\item Spec Resolve: If the resolve predicate is true, resolution occurs for one speculation level. In contrast to Fences, resolve does not necessarily kill all speculation levels, but allows resolution one level at a time
\end{itemize}\<close>
inductive
stepS :: "configS \<Rightarrow> configS \<Rightarrow> bool" (infix \<open>\<rightarrow>S\<close> 55)
where 
nonspec_normal: 
"cfgs = [] \<Longrightarrow>  
 \<not> is_IfJump (prog!(pcOf cfg)) \<or> \<not> mispred pstate [pcOf cfg] \<Longrightarrow> 
 pstate' = pstate \<Longrightarrow> 
 \<not> finalB (cfg, ibT, ibUT) \<Longrightarrow> (cfg', ibT', ibUT') = nextB (cfg, ibT, ibUT) \<Longrightarrow> 
 cfgs' = [] \<Longrightarrow> 
 ls' = ls \<union> readLocs cfg
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')"
|
nonspec_mispred: 
"cfgs = [] \<Longrightarrow> 
 is_IfJump (prog!(pcOf cfg)) \<Longrightarrow> mispred pstate [pcOf cfg] \<Longrightarrow> 
 pstate' = update pstate [pcOf cfg] \<Longrightarrow> 
 \<not> finalM (cfg, ibT, ibUT) \<Longrightarrow> (cfg', ibT', ibUT') = nextB (cfg, ibT, ibUT) \<Longrightarrow> (cfg1', ibT1', ibUT1') = nextM (cfg, ibT, ibUT) \<Longrightarrow> 
 cfgs' = [cfg1'] \<Longrightarrow> 
 ls' = ls \<union> readLocs cfg
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')" 
|
spec_normal: 
"cfgs \<noteq> [] \<Longrightarrow> 
 \<not> resolve pstate (pcOf cfg # map pcOf cfgs)  \<Longrightarrow> 
 \<not> is_IfJump (prog!(pcOf (last cfgs))) \<or> \<not> mispred pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow> 
 prog!(pcOf (last cfgs)) \<noteq> Fence \<Longrightarrow>
 pstate' = pstate \<Longrightarrow> 
 \<not> is_getInput (prog!(pcOf (last cfgs))) \<Longrightarrow>
 \<not> is_Output (prog!(pcOf (last cfgs))) \<Longrightarrow> 
 \<not> finalB (last cfgs, ibT, ibUT) \<Longrightarrow> (cfg1',ibT', ibUT') = nextB (last cfgs, ibT, ibUT) \<Longrightarrow> 
 cfg' = cfg \<Longrightarrow> cfgs' = butlast cfgs @ [cfg1'] \<Longrightarrow> 
 ls' = ls \<union> readLocs (last cfgs)
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')"
|
spec_mispred: 
"cfgs \<noteq> [] \<Longrightarrow> 
 \<not> resolve pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow> 
 is_IfJump (prog!(pcOf (last cfgs))) \<Longrightarrow> mispred pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow> 
 pstate' = update pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow> 
 \<not> finalM (last cfgs, ibT, ibUT) \<Longrightarrow> 
 (lcfg', ibT', ibUT') = nextB (last cfgs, ibT, ibUT) \<Longrightarrow> (cfg1', ibT1', ibUT1') = nextM (last cfgs, ibT, ibUT) \<Longrightarrow> 
 cfg' = cfg \<Longrightarrow> cfgs' = butlast cfgs @ [lcfg'] @ [cfg1'] \<Longrightarrow> 
 ls' = ls \<union> readLocs (last cfgs)
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')"
|
spec_Fence: 
"cfgs \<noteq> [] \<Longrightarrow> 
 \<not> resolve pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow> 
 prog!(pcOf (last cfgs)) = Fence \<Longrightarrow>
 pstate' = pstate \<Longrightarrow> cfg' = cfg \<Longrightarrow> cfgs' = [] \<Longrightarrow> 
 ibT = ibT' \<Longrightarrow> ibUT = ibUT' \<Longrightarrow> ls' = ls 
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')"
|
spec_resolve: 
"cfgs \<noteq> [] \<Longrightarrow> 
 resolve pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow>  
 pstate' = update pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow>
 cfg' = cfg \<Longrightarrow> cfgs' = butlast cfgs \<Longrightarrow> 
 ibT = ibT' \<Longrightarrow> ibUT = ibUT' \<Longrightarrow> ls' = ls 
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')"

lemmas stepS_induct = stepS.induct[split_format(complete)]

(* *)
subsubsection "State Transitions"
lemma stepS_nonspec_normal_iff[simp]: 
"cfgs = [] \<Longrightarrow> \<not> is_IfJump (prog!(pcOf cfg)) \<or> \<not> mispred pstate [pcOf cfg]  
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')
 \<longleftrightarrow> 
 (pstate' = pstate \<and> \<not> finalB (cfg, ibT, ibUT) \<and> 
  (cfg', ibT', ibUT') = nextB (cfg, ibT, ibUT) \<and> 
  cfgs' = [] \<and> ls' = ls \<union> readLocs cfg)"
apply(subst stepS.simps) by auto

lemma stepS_nonspec_normal_iff1[simp]: 
"cfgs = [] \<Longrightarrow> \<not> is_IfJump (prog!pc) \<or> \<not> mispred pstate [pc]  
 \<Longrightarrow> 
 (pstate, (Config pc (State (Vstore vs) avst h p)), cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', (Config pc' (State (Vstore vs') avst' h' p')), cfgs', ibT', ibUT', ls')
 \<longleftrightarrow> 
 (pstate' = pstate \<and> \<not> finalB ((Config pc (State (Vstore vs) avst h p)), ibT, ibUT) \<and> 
  ((Config pc' (State (Vstore vs') avst' h' p')), ibT', ibUT') = nextB ((Config pc (State (Vstore vs) avst h p)), ibT, ibUT) \<and> 
  cfgs' = [] \<and> ls' = ls \<union> readLocs (Config pc (State (Vstore vs) avst h p)))"
  using stepS_nonspec_normal_iff config.sel(1) by presburger


lemma stepS_nonspec_mispred_iff[simp]: 
"cfgs = [] \<Longrightarrow> is_IfJump (prog!(pcOf cfg)) \<Longrightarrow> mispred pstate [pcOf cfg]
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')
 \<longleftrightarrow> 
 (\<exists>cfg1' ibT1' ibUT1'. pstate' = update pstate [pcOf cfg] \<and> 
  \<not> finalM (cfg, ibT, ibUT) \<and> (cfg', ibT', ibUT') = nextB (cfg, ibT, ibUT) \<and>
  (cfg1', ibT1', ibUT1') = nextM (cfg, ibT, ibUT) \<and> 
  cfgs' = [cfg1'] \<and> ls' = ls \<union> readLocs cfg)" 
apply(subst stepS.simps) by auto

lemma stepS_spec_normal_iff[simp]: 
"cfgs \<noteq> [] \<Longrightarrow> 
 \<not> resolve pstate (pcOf cfg # map pcOf cfgs)  \<Longrightarrow> 
 \<not> is_IfJump (prog!(pcOf (last cfgs))) \<or> \<not> mispred pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow> 
 prog!(pcOf (last cfgs)) \<noteq> Fence 
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')
 \<longleftrightarrow>
 (\<exists>cfg1'. pstate' = pstate \<and> 
    \<not> is_getInput (prog!(pcOf (last cfgs))) \<and>
    \<not> is_getInput (prog!(pcOf (last cfgs))) \<and> \<not> is_Output (prog!(pcOf (last cfgs))) \<and> 
    \<not> finalB (last cfgs, ibT, ibUT) \<and> (cfg1',ibT',ibUT') = nextB (last cfgs, ibT, ibUT) \<and>  
    cfg' = cfg \<and> cfgs' = butlast cfgs @ [cfg1'] \<and> ls' = ls \<union> readLocs (last cfgs))"
apply(subst stepS.simps) by auto

lemma stepS_spec_mispred_iff[simp]: 
"cfgs \<noteq> [] \<Longrightarrow> 
 \<not> resolve pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow> 
 is_IfJump (prog!(pcOf (last cfgs))) \<Longrightarrow> mispred pstate (pcOf cfg # map pcOf cfgs)
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')
 \<longleftrightarrow> 
 (\<exists>cfg1' ibT1' ibUT1' lcfg'. pstate' = update pstate (pcOf cfg # map pcOf cfgs) \<and> 
  \<not> finalM (last cfgs, ibT, ibUT) \<and> 
  (lcfg', ibT', ibUT') = nextB (last cfgs, ibT, ibUT) \<and> 
  (cfg1', ibT1', ibUT1') = nextM (last cfgs, ibT, ibUT) \<and> 
  cfg' = cfg \<and> cfgs' = butlast cfgs @ [lcfg'] @ [cfg1'] \<and> ls' = ls \<union> readLocs (last cfgs))"
apply(subst stepS.simps) by auto

lemma stepS_spec_Fence_iff[simp]: 
"cfgs \<noteq> [] \<Longrightarrow> 
 \<not> resolve pstate (pcOf cfg # map pcOf cfgs) \<Longrightarrow> 
 prog!(pcOf (last cfgs)) = Fence 
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')
 \<longleftrightarrow>
 (pstate' = pstate \<and> cfg = cfg' \<and> cfgs' = [] \<and> ibT' = ibT \<and> ibUT' = ibUT \<and> ls' = ls)"
apply(subst stepS.simps) by auto

lemma stepS_spec_resolve_iff[simp]: 
"cfgs \<noteq> [] \<Longrightarrow> 
 resolve pstate (pcOf cfg # map pcOf cfgs)
 \<Longrightarrow> 
 (pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')
 \<longleftrightarrow>
 (pstate' = update pstate (pcOf cfg # map pcOf cfgs) \<and>
  cfg' = cfg \<and> cfgs' = butlast cfgs \<and> ibT' = ibT \<and> ibUT' = ibUT \<and> ls' = ls)"
apply(subst stepS.simps) by auto

(* *)

lemma stepS_cases[cases pred: stepS, 
 consumes 1, 
 case_names nonspec_normal nonspec_mispred 
            spec_normal spec_mispred spec_Fence spec_resolve]:
assumes "(pstate, cfg, cfgs, ibT, ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT', ibUT', ls')"
obtains 
(* nonspec_normal: *)
"cfgs = []"  
   "\<not> is_IfJump (prog!(pcOf cfg)) \<or> \<not> mispred pstate [pcOf cfg]"
   "pstate' = pstate"
   "\<not> finalB (cfg, ibT, ibUT)"
   "(cfg', ibT', ibUT') = nextB (cfg, ibT, ibUT)"
   "cfgs' = []"
   "ls' = ls \<union> readLocs cfg"
| 
(* nonspec_mispred *)
"cfgs = []" 
   "is_IfJump (prog!(pcOf cfg))" "mispred pstate [pcOf cfg]"
   "pstate' = update pstate [pcOf cfg]"
   "\<not> finalM (cfg, ibT, ibUT)"
   "(cfg', ibT', ibUT') = nextB (cfg, ibT, ibUT)"
   "\<exists>cfg1' ibT1' ibUT1'. (cfg1', ibT1', ibUT1') = nextM (cfg, ibT, ibUT) 
                \<and> cfgs' = [cfg1']"
   "ls' = ls \<union> readLocs cfg"
|
(* spec_normal *)
"cfgs \<noteq> []" 
   "\<not> resolve pstate (pcOf cfg # map pcOf cfgs)"
      "\<not> is_IfJump (prog!(pcOf (last cfgs))) \<or> \<not> mispred pstate (pcOf cfg # map pcOf cfgs)"
      "prog!(pcOf (last cfgs)) \<noteq> Fence"
      "pstate' = pstate"
      "\<not> is_getInput (prog!(pcOf (last cfgs)))"
      "\<not> is_Output (prog!(pcOf (last cfgs)))"
      "cfg' = cfg"
      "ls' = ls \<union> readLocs (last cfgs)"
      "\<exists>cfg1'. nextB (last cfgs, ibT, ibUT) = (cfg1',ibT',ibUT')
           \<and> cfgs' = butlast cfgs @ [cfg1']"
|
(* spec_mispred:  *) 
"cfgs \<noteq> []"
   "\<not> resolve pstate (pcOf cfg # map pcOf cfgs)" 
      "is_IfJump (prog!(pcOf (last cfgs)))" "mispred pstate (pcOf cfg # map pcOf cfgs)"
      "pstate' = update pstate (pcOf cfg # map pcOf cfgs)"
      "\<not> finalM (last cfgs, ibT, ibUT)"
      "cfg' = cfg"
      "\<exists>lcfg' cfg1' ibT1' ibUT1'. 
       nextB (last cfgs, ibT, ibUT) = (lcfg',ibT',ibUT') \<and>
       (cfg1', ibT1', ibUT1') = nextM (last cfgs, ibT, ibUT) \<and>
       cfgs' = butlast cfgs @ [lcfg'] @ [cfg1']" 
      "ls' = ls \<union> readLocs (last cfgs)"
|
(* spec_Fence: *)
"cfgs \<noteq> []"
   "\<not> resolve pstate (pcOf cfg # map pcOf cfgs)"
      "prog!(pcOf (last cfgs)) = Fence"
      "pstate' = pstate"
      "cfg' = cfg"
      "cfgs' = []"
      "ibT' = ibT" 
      "ibUT' = ibUT" 
      "ls' = ls"
|
(* spec_resolve: *)
"cfgs \<noteq> []"   
   "resolve pstate (pcOf cfg # map pcOf cfgs)"
   "pstate' = update pstate (pcOf cfg # map pcOf cfgs)"
   "cfg' = cfg"
   "cfgs' = butlast cfgs"
   "ls' = ls"
   "ibT' = ibT" 
   "ibUT' = ibUT" 
  using assms by (cases rule: stepS.cases, metis+) 
(* *)
lemma stepS_endPC: "pcOf cfg = endPC \<Longrightarrow> \<not> (pstate, cfg, [], ibT, ibUT, ls) \<rightarrow>S ss'"
apply(cases ss') 
apply safe apply(cases rule: stepS_cases, auto) 
  using finalB_endPC apply blast  
  using finalB_endPC apply blast
  using finalB_endPC finalB_imp_finalM by blast

abbreviation
  stepsS :: "configS \<Rightarrow> configS \<Rightarrow> bool" (infix \<open>\<rightarrow>S*\<close> 55)
  where "x \<rightarrow>S* y \<equiv> star stepS x y"

definition "finalS = final stepS"
lemmas finalS_defs  = final_def finalS_def

lemma stepS_0: "(pstate, Config 0 s, [], ibT, ibUT, ls) \<rightarrow>S (pstate, Config 1 s, [], ibT, ibUT, ls)"
using prog_0 apply-apply(rule nonspec_normal) 
using One_nat_def stebB_0 stepB_nextB  
by (auto simp: readLocs_def finalB_def final_def, meson)

lemma stepS_imp_stepB:"(pstate, cfg, [], ibT,ibUT, ls) \<rightarrow>S (pstate', cfg', cfgs', ibT',ibUT', ls') \<Longrightarrow> (cfg, ibT,ibUT) \<rightarrow>B (cfg', ibT',ibUT')"
  subgoal premises s
    using s apply (cases rule: stepS_cases)
    by (metis finalB_imp_finalM stepB_iff_nextB)+ .

subsubsection "Elimination Rules"

(*step2 elims*)
lemma stepS_Assign2E:
  assumes \<open>(ps3, cfg3, cfgs3, ibT3,ibUT3, ls3) \<rightarrow>S (ps3', cfg3', cfgs3', ibT3',ibUT3', ls3')\<close> 
      and \<open>(ps4, cfg4, cfgs4, ibT4,ibUT4, ls4) \<rightarrow>S (ps4', cfg4', cfgs4', ibT4',ibUT4', ls4')\<close>
      and \<open>cfg3 = (Config pc3 (State (Vstore vs3) avst3 h3 p3))\<close> and \<open>cfg3' = (Config pc3' (State (Vstore vs3') avst3' h3' p3'))\<close>
      and \<open>cfg4 = (Config pc4 (State (Vstore vs4) avst4 h4 p4))\<close> and \<open>cfg4' = (Config pc4' (State (Vstore vs4') avst4' h4' p4'))\<close>
      and \<open>cfgs3 = []\<close> and \<open>cfgs4 = []\<close>
      and \<open>prog!pc3 = (x ::= a)\<close> and \<open>pcOf cfg3 = pcOf cfg4\<close> 
    shows \<open>cfgs3' = [] \<and> cfgs4' = [] \<and> 
           vs3' = (vs3(x := aval a (stateOf cfg3))) \<and>
           vs4' = (vs4(x := aval a (stateOf cfg4))) \<and>
           pc3' = Suc pc3 \<and> pc4' = Suc pc4 \<and> ls4' = ls4 \<union> readLocs cfg4 \<and>
           avst3' = avst3 \<and> avst4' = avst4 \<and> ls3' = ls3 \<union> readLocs cfg3 \<and>
           p3 = p3' \<and> p4 = p4'\<close>
  using assms apply clarify 
  apply-apply(frule stepS_imp_stepB[of ps3])
  apply(frule stepS_imp_stepB[of ps4])
  apply (drule stepB_AssignE[of _ _ _ _ _ _ pc3 vs3 avst3 h3 p3
                                pc3' vs3' avst3' h3' p3' x a], clarify+)
  apply (drule stepB_AssignE[of _ _ _ _ _ _ pc4 vs4 avst4 h4 p4
                                pc4' vs4' avst4' h4' p4'], clarify+)
  by fastforce+


end (* context Prog_Mispred *)

end