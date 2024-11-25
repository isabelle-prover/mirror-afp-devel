section \<open>Relative Security instantiation - Common Aspects\<close>

text \<open> This theory sets up a generic instantiaton infrastructure for all our running examples. For a detailed explanation of each example and it's (dis)proof of Relative Security see the work by Dongol et al. \cite{RS}\<close>


theory Instance_Common
imports "../IMP/Step_Normal" "../IMP/Step_Spec" 
begin



no_notation bot ("\<bottom>")
(* This will be used for non-informative entities, e.g., a noninformative output: *)
abbreviation noninform ("\<bottom>") where "\<bottom> \<equiv> undefined"


(* Avoid splitting the quantifiers over product types into two quantifiers *)
declare split_paired_All[simp del]
declare split_paired_Ex[simp del]

(*  *)
(*mis-speculation cases*)
definition noMisSpec where "noMisSpec (cfgs::config list) \<equiv> (cfgs = [])"
lemma noMisSpec_ext[simp]:"map x cfgs = map x cfgs' \<Longrightarrow> noMisSpec cfgs \<longleftrightarrow> noMisSpec cfgs'"
  by (auto simp: noMisSpec_def)
(* mis-speculation of nestedness level 1: *)
definition misSpecL1 where "misSpecL1 (cfgs::config list) \<equiv> (length cfgs = Suc 0)"
lemma misSpecL1_len[simp]:"misSpecL1 cfgs \<longleftrightarrow> length cfgs = 1" by (simp add: misSpecL1_def)
(*level 2*)
definition misSpecL2 where "misSpecL2 (cfgs::config list) \<equiv> (length cfgs = 2)"





(* *)
fun tuple::"'a \<times> 'b \<times> 'c \<Rightarrow> 'a \<times> 'b"
  where "tuple (a,b,c) = (a,b)"

fun tuple_sel::"'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e  \<Rightarrow> 'b \<times> 'd"
  where "tuple_sel (a,b,c,d,e) = (b,d)"

fun cfgsOf::"'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e  \<Rightarrow> 'c"
  where "cfgsOf (a,b,c,d,e) = c"

fun pstateOf::"'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e  \<Rightarrow> 'a"
  where "pstateOf (a,b,c,d,e) = a"

fun stateOfs::"'a \<times> 'b \<times> 'c \<times> 'd \<times> 'e  \<Rightarrow> 'b"
  where "stateOfs (a,b,c,d,e) = b"

(*  *)

context Prog_Mispred
begin
text \<open>The "vanilla-semantics" transitions are the normal executions (featuring no speculation):\<close>

text \<open>Vanilla-semantics system model: given by the normal semantics\<close>
type_synonym stateV = "config \<times> val llist \<times> val llist \<times> loc set"
fun validTransV where "validTransV (cfg_ib_ls,cfg_ib_ls') = cfg_ib_ls \<rightarrow>N cfg_ib_ls'"

text \<open>Vanilla-semantics observation infrastructure (part of the vanilla-semantics state-wise attacker model): \<close>
text \<open>The attacker observes the output value, the program counter history and the set of accessed locations so far:\<close>
type_synonym obsV = "val \<times> loc set"
text \<open>The attacker-action is just a value (used as input to the function):\<close>
type_synonym actV = "val"
text \<open>The attacker's interaction\<close>
fun isIntV :: "stateV \<Rightarrow> bool" where 
"isIntV ss = (\<not> finalN ss)"
text \<open>The attacker interacts with the system by passing input to the function and 
reading the outputs (standard channel) and the accessed locations (side channel) \<close>
fun getIntV :: "stateV \<Rightarrow> actV \<times> obsV" where 
"getIntV (cfg,ibT,ibUT,ls) = 
 (case prog!(pcOf cfg) of 
    Input T _ \<Rightarrow> (lhd ibT, \<bottom>)
   |Input U _ \<Rightarrow> (lhd ibUT, \<bottom>)
   |Output U _ \<Rightarrow> (\<bottom>, (outOf (prog!(pcOf cfg)) (stateOf cfg), ls))
   |_ \<Rightarrow> (\<bottom>,\<bottom>)
 )"

lemma validTransV_iff_nextN: "validTransV (s1, s2) = (\<not> finalN s1 \<and> nextN s1 = s2)"
  by (simp add: stepN_iff_nextN)+
(* *)

text \<open>The optimization-enhanced semantics system model: given by the speculative semantics\<close>
type_synonym stateO = configS
fun validTransO where "validTransO (cfgS,cfgS') = cfgS \<rightarrow>S cfgS'"

text \<open>Optimization-enhanced semantics observation infrastructure (part of the optimization-enhanced semantics state-wise attacker model):
similar to that of the vanilla semantics, in that the standard-channel inputs and outputs are those produced by the normal execution.  
However, the side-channel outputs (the sets of read locations) are also collected.\<close>
type_synonym obsO = "val \<times> loc set"
type_synonym actO = "val"
fun isIntO :: "stateO \<Rightarrow> bool" where 
"isIntO ss = (\<not> finalS ss)"
fun getIntO :: "stateO \<Rightarrow> actO \<times> obsO" where 
"getIntO (pstate,cfg,cfgs,ibT,ibUT,ls) = 
 (case (cfgs, prog!(pcOf cfg)) of 
    ([],Input T _) \<Rightarrow> (lhd ibT, \<bottom>)
   |([],Input U _) \<Rightarrow> (lhd ibUT, \<bottom>)
   |([],Output U _) \<Rightarrow> 
      (\<bottom>, (outOf (prog!(pcOf cfg)) (stateOf cfg), ls))
   |_ \<Rightarrow> (\<bottom>,\<bottom>)
 )"

end (* context Prog_Mispred *)


locale Prog_Mispred_Init = 
Prog_Mispred prog mispred resolve update 
for prog :: "com list"
and mispred :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool"
and resolve :: "predState \<Rightarrow> pcounter list \<Rightarrow> bool"
and update :: "predState \<Rightarrow> pcounter list \<Rightarrow> predState"
+ 
fixes initPstate :: predState
  and istate :: "state \<Rightarrow> bool"
begin

fun istateV :: "stateV \<Rightarrow> bool" where 
"istateV (cfg, ibT, ibUT, ls) \<longleftrightarrow> 
  pcOf cfg = 0 \<and> istate (stateOf cfg) \<and>
  llength ibT = \<infinity> \<and> llength ibUT = \<infinity> \<and>
  ls = {}"

fun istateO :: "stateO \<Rightarrow> bool" where 
"istateO (pstate, cfg, cfgs, ibT,ibUT, ls) \<longleftrightarrow> 
  pstate = initPstate \<and> 
  pcOf cfg = 0 \<and> ls = {} \<and>  
  istate (stateOf cfg) \<and> 
  cfgs = [] \<and> llength ibT = \<infinity> \<and> llength ibUT = \<infinity>"

(* Some auxiliary definitions and facts: *)

lemma istateV_config_imp:
"istateV (cfg, ibT,ibUT, ls) \<Longrightarrow> pcOf cfg = 0 \<and> ls = {} \<and> ibT \<noteq> LNil"
  by force

lemma istateO_config_imp:
"istateO (pstate,cfg,cfgs,ibT,ibUT,ls) \<Longrightarrow>
 cfgs = [] \<and> pcOf cfg = 0 \<and> ls = {} \<and> ibT \<noteq> LNil"
  unfolding istateO.simps
  by auto

(* *)

(*same variable for all cfgs*)
definition "same_var_all x cfg1 cfg2 cfg3 cfgs3 cfg4 cfgs4 \<equiv> 
 vstore (getVstore (stateOf cfg1)) x = vstore (getVstore (stateOf cfg4)) x \<and>
 vstore (getVstore (stateOf cfg2)) x = vstore (getVstore (stateOf cfg4)) x \<and>
 vstore (getVstore (stateOf cfg3)) x = vstore (getVstore (stateOf cfg4)) x \<and>
 (\<forall>cfg3'\<in>set cfgs3. vstore (getVstore (stateOf cfg3')) x = vstore (getVstore (stateOf cfg3)) x) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. vstore (getVstore (stateOf cfg4')) x = vstore (getVstore (stateOf cfg4)) x)"

(*same variable for cfg1 and cfg2*)
definition "same_var x cfg cfg' \<equiv> 
  vstore (getVstore (stateOf cfg)) x = vstore (getVstore (stateOf cfg')) x"

(*same variable for cfg1 and cfg2, value provided*)
definition "same_var_val x (val::int) cfg cfg' \<equiv> 
  vstore (getVstore (stateOf cfg)) x = vstore (getVstore (stateOf cfg')) x \<and>
  vstore (getVstore (stateOf cfg)) x = val"


(*We want the originals to have the same action, but making sure i \<ge> N*)
definition "same_var_o ii cfg3 cfgs3 cfg4 cfgs4 \<equiv> 
 vstore (getVstore (stateOf cfg3)) ii = vstore (getVstore (stateOf cfg4)) ii \<and>
 (\<forall>cfg3'\<in>set cfgs3. vstore (getVstore (stateOf cfg3')) ii = vstore (getVstore (stateOf cfg3)) ii) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. vstore (getVstore (stateOf cfg4')) ii = vstore (getVstore (stateOf cfg4)) ii)"


lemma set_var_shrink:"\<forall>cfg3'\<in>set cfgs.
           vstore (getVstore (stateOf cfg3')) var =
           vstore (getVstore (stateOf cfg)) var 
       \<Longrightarrow>       
       \<forall>cfg3'\<in>set (butlast cfgs).
           vstore (getVstore (stateOf cfg3')) var =
           vstore (getVstore (stateOf cfg)) var"
  by (meson in_set_butlastD)


lemma heapSimp:"(\<forall>cfg''\<in>set cfgs''. getHheap (stateOf cfg') = getHheap (stateOf cfg'')) \<and> cfgs'' \<noteq> []
\<Longrightarrow> getHheap (stateOf cfg') = getHheap (stateOf (last cfgs''))"
  by simp

lemma heapSimp2:"(\<forall>cfg''\<in>set cfgs''. getHheap (stateOf cfg') = getHheap (stateOf cfg'')) \<and> cfgs'' \<noteq> []

\<Longrightarrow> getHheap (stateOf cfg') = getHheap (stateOf (hd cfgs''))"
  by simp

lemma array_baseSimp:"array_base aa1 (getAvstore (stateOf cfg)) =
 array_base aa1 (getAvstore (stateOf cfg')) \<and> 
 (\<forall>cfg'\<in>set cfgs. array_base aa1 (getAvstore (stateOf cfg')) =
   array_base aa1 (getAvstore (stateOf cfg)))
\<and> cfgs \<noteq> []
\<Longrightarrow> 
 array_base aa1 (getAvstore (stateOf cfg)) =
 array_base aa1 (getAvstore (stateOf (last cfgs)))
"
  by simp

lemma finalB_imp_finalS:"finalB (cfg, ibT,ibUT) \<Longrightarrow> (\<forall>pstate cfgs ls. finalS (pstate, cfg, [], ibT,ibUT, ls))"
  unfolding finalB_def finalS_def final_def apply clarsimp
    subgoal for pstate ls pstate' cfg' cfgs' ibT ibUT' ls'
      apply(erule allE[of _ "(cfg', ibT,ibUT')"])
      subgoal premises step 
        using step(1) apply (cases rule: stepS_cases)
        using finalB_imp_finalM step(2) nextB_stepB by (simp_all, blast) . .

lemma cfgs_Suc_zero[simp]:"length cfgs = Suc 0 \<Longrightarrow> cfgs = [last cfgs]"
  by (metis Suc_length_conv last_ConsL length_0_conv)

lemma cfgs_map[simp]:"length cfgs = Suc 0 \<Longrightarrow> map pcOf cfgs = [pcOf (last cfgs)]"
  apply(frule cfgs_Suc_zero[of cfgs])
  apply(rule ssubst[of "map pcOf cfgs" "map pcOf [last cfgs]"]) 
  by (presburger,metis list.simps(8,9))

end (* context Prog_Mispred_Init *)


end 
