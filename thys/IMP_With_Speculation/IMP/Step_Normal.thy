section "Normal Semantics"

text \<open> This theory augments the basic semantics to include a set of read locations which is a simple representation of a cache\<close>
text \<open>The normal semantics is defined by a single rule which involves the basic semantics, extended to accumulate the read locations, which accounts for cache side-channels \<close>

theory Step_Normal
imports Step_Basic
begin


context Prog 
begin

fun stepN :: "config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> bool" (infix \<open>\<rightarrow>N\<close> 55)
where
"(cfg,ibT,ibUT,ls) \<rightarrow>N (cfg',ibT',ibUT',ls') =
 ((cfg,ibT,ibUT) \<rightarrow>B (cfg',ibT',ibUT') \<and> ls' = ls \<union> readLocs cfg)"

abbreviation
  stepsN :: "config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> bool" (infix \<open>\<rightarrow>N*\<close> 55)
  where "x \<rightarrow>N* y == star stepN x y"


(* *)

definition "finalN = final stepN"
lemmas finalN_defs  = final_def finalN_def

lemma finalN_iff_finalB[simp]: 
"finalN (cfg, ibT, ibUT, ls) \<longleftrightarrow> finalB (cfg, ibT, ibUT)"
unfolding finalN_def finalB_def final_def by auto

(* *)

subsection "State Transitions"
fun nextN :: "config \<times> val llist \<times> val llist \<times> loc set \<Rightarrow> config \<times> val llist \<times> val llist \<times> loc set" where 
"nextN (cfg, ibT, ibUT, ls) = (case nextB (cfg,ibT,ibUT) of (cfg',ibT',ibUT') \<Rightarrow> (cfg',ibT',ibUT',ls \<union> readLocs cfg))"
 
lemma nextN_stepN: "\<not> finalN cfg_ib_ls \<Longrightarrow> cfg_ib_ls \<rightarrow>N (nextN cfg_ib_ls)"
apply(cases cfg_ib_ls) 
  using Prog.stepB_nextB Prog_axioms finalN_def 
        final_def nextN.simps old.prod.case stepN.elims(2) 
  by force

lemma stepN_nextN: "cfg_ib_ls \<rightarrow>N cfg'_ib'_ls' \<Longrightarrow> cfg'_ib'_ls' = nextN cfg_ib_ls"
apply(cases cfg_ib_ls) apply(cases cfg'_ib'_ls') 
using Prog.stepB_nextB Prog_axioms by auto

lemma nextN_iff_stepN: 
"\<not> finalN cfg_ib_ls \<Longrightarrow> nextN cfg_ib_ls  = cfg'_ib'_ls' \<longleftrightarrow> cfg_ib_ls \<rightarrow>N cfg'_ib'_ls'"
using nextN_stepN stepN_nextN by blast

lemma stepN_iff_nextN: "cfg_ib_ls \<rightarrow>N cfg'_ib'_ls' \<longleftrightarrow> \<not> finalN cfg_ib_ls \<and> nextN cfg_ib_ls  = cfg'_ib'_ls'"
by (metis finalN_def final_def stepN_nextN)

(* *)

lemma finalN_endPC: "pcOf cfg = endPC \<Longrightarrow> finalN (cfg,ibT,ibUT)"
  by (metis finalN_iff_finalB finalB_endPC old.prod.exhaust)

lemma stepN_endPC: "pcOf cfg = endPC \<Longrightarrow> \<not> (cfg,ibT,ibUT) \<rightarrow>N (cfg',ibT',ibUT')"
  by (simp add: finalN_endPC stepN_iff_nextN) 

lemma stebN_0: "(Config 0 s, ibT, ibUT, ls) \<rightarrow>N (Config 1 s, ibT, ibUT, ls)"
using prog_0 One_nat_def stebB_0 by (auto simp: readLocs_def)


lemma finalB_eq_finalN:"finalB (cfg, ibT,ibUT) \<longleftrightarrow> (\<forall>ls. finalN (cfg, ibT,ibUT, ls))"
  unfolding finalN_defs finalB_def
  apply standard by auto


subsection "Elimination Rules"
(*step2 elims*)
lemma stepN_Assign2E:
  assumes \<open>(cfg1, ibT1,ibUT1, ls1) \<rightarrow>N (cfg1', ibT1',ibUT1', ls1')\<close> 
      and \<open>(cfg2, ibT2,ibUT2, ls2) \<rightarrow>N (cfg2', ibT2',ibUT2', ls2')\<close>
      and \<open>cfg1 = (Config pc1 (State (Vstore vs1) avst1 h1 p1))\<close> and \<open>cfg1' = (Config pc1' (State (Vstore vs1') avst1' h1' p1'))\<close>
      and \<open>cfg2 = (Config pc2 (State (Vstore vs2) avst2 h2 p2))\<close> and \<open>cfg2' = (Config pc2' (State (Vstore vs2') avst2' h2' p2'))\<close>
      and \<open>prog!pc1 = (x ::= a)\<close> and \<open>pcOf cfg1 = pcOf cfg2\<close> 
    shows \<open>vs1' = (vs1(x := aval a (stateOf cfg1))) \<and> ibT1 = ibT1' \<and> ibUT1 = ibUT1' \<and>
           vs2' = (vs2(x := aval a (stateOf cfg2))) \<and> ibT2 = ibT2' \<and> ibUT2 = ibUT2' \<and>
           pc1' = Suc pc1 \<and> pc2' = Suc pc2 \<and> ls2' = ls2 \<union> readLocs cfg2 \<and>
           avst1' = avst1 \<and> avst2' = avst2 \<and> ls1' = ls1 \<union> readLocs cfg1\<close>
  using assms apply clarsimp
  apply (drule stepB_AssignE[of _ _ _ _ _ _ pc1 vs1 avst1 h1 p1
                                pc1' vs1' avst1' h1' p1' x a], clarify+)
  apply (drule stepB_AssignE[of _ _ _ _ _ _ pc2 vs2 avst2 h2 p2
                                pc2' vs2' avst2' h2' p2' x a], clarify+)
  by auto


lemma stepN_Seq_Start_Skip_Fence2E:
  assumes \<open>(cfg1, ibT1,ibUT1, ls1) \<rightarrow>N (cfg1', ibT1',ibUT1', ls1')\<close> 
      and \<open>(cfg2, ibT2,ibUT2, ls2) \<rightarrow>N (cfg2', ibT2',ibUT2', ls2')\<close>
      and \<open>cfg1 = (Config pc1 (State (Vstore vs1) avst1 h1 p1))\<close> and \<open>cfg1' = (Config pc1' (State (Vstore vs1') avst1' h1' p1'))\<close>
      and \<open>cfg2 = (Config pc2 (State (Vstore vs2) avst2 h2 p2))\<close> and \<open>cfg2' = (Config pc2' (State (Vstore vs2') avst2' h2' p2'))\<close>
      and \<open>prog!pc1 \<in> {Start, Skip, Fence}\<close> and \<open>pcOf cfg1 = pcOf cfg2\<close> 
    shows \<open>vs1' = vs1 \<and> vs2' = vs2 \<and>
           pc1' = Suc pc1 \<and> pc2' = Suc pc2 \<and>
           avst1' = avst1 \<and> avst2' = avst2 \<and> 
           ls2' = ls2 \<and> ls1' = ls1\<close>
  using assms apply clarsimp
  apply (drule stepB_Seq_Start_Skip_FenceE[of _ _ _ _ _ _ pc1 vs1 avst1 h1 p1
                                pc1' vs1' avst1' h1' p1'], clarify+)
  apply (drule stepB_Seq_Start_Skip_FenceE[of _ _ _ _ _ _ pc2 vs2 avst2 h2 p2
                                pc2' vs2' avst2' h2' p2'], clarify+)
  by (auto simp add: readLocs_def)

end (* locale Prog *)


end