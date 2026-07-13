(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)
subsection "Sprenger-Dam Criterion Incompleteness"

theory SD_Incomplete
imports "../Incomplete_Criteria"
begin

(* SPRENGER-DAM INCOMPLETE *)
(*A counter example to show incompleteness*)
(*types*)
datatype node = One
datatype pos= h1 | h1'

(*Nodes, Edges, Positions and Relations between them*)
definition "Node \<equiv> {One}"

lemma O_Node[simp]:"One \<in> Node" by(simp add: Node_def)

lemma alw_nodes:"alw (holdsS Node) nds" 
  unfolding alw_holdsS_iff_snth Node_def apply(rule allI)
  subgoal for i apply(induct i)
    using node.exhaust by auto .
    

fun edge::"node \<Rightarrow> node \<Rightarrow> bool" where
"edge One One = HOL.True"

lemma edge_into_zero:"edge nd nd' \<longleftrightarrow> nd = One \<and> nd' = One" by(cases nd, cases nd', auto)

lemma edgeTrue:"edge nd nd'" by(cases nd, cases nd', auto)

fun PosOf::"node \<Rightarrow> pos set" where 
"PosOf One = {h1, h1'}"


(*sets relating positions together*)
definition RR_set :: "((node \<times> pos) \<times> (node \<times> pos) \<times> slope) set" where
  "RR_set = {
     ((One, h1), (One, h1'), Decr),

     ((One, h1'), (One, h1), Main)
 }"


definition RR :: "node \<times> pos \<Rightarrow> node \<times> pos \<Rightarrow> slope \<Rightarrow> bool" where
  "RR np1 np2 s \<equiv> ((np1, np2, s) \<in> RR_set)"

lemmas RR_defs = RR_def RR_set_def

lemma RR_ZO[simp]:"RR (One, h1) (One, h1') Decr" unfolding RR_defs by auto
lemma RR_OZ[simp]:"RR (One, h1') (One, h1) Main" unfolding RR_defs by auto

(*RR sound*)
lemma P_inPosOf:"RR (nd, P) (nd', P') sl \<Longrightarrow> P \<in> PosOf nd"
                 "RR (nd, P) (nd', P') sl \<Longrightarrow> P' \<in> PosOf nd'" by(auto simp: RR_defs)

interpretation Sloped_Graph where 
    Node = Node and edge = edge and PosOf = PosOf
    and RR = RR apply standard
  subgoal by(simp add: Node_def)
  subgoal by(unfold Node_def, auto elim: PosOf.cases)
  by(auto simp: RR_defs SlopedRels_def Node_def)

lemma allNodesOne:"\<forall>i. nds !! i = One" using alw_nodes[unfolded Node_def, of nds] PosOf.cases by auto

lemma ipath_isOne:"ipath nds \<Longrightarrow> nds = sconst One"
  using allNodesOne unfolding ipath_iff_snth
  by (simp add: snth_equalityI)


lemma j_mod2_cases:"((j mod Suc (Suc 0)) = 0 \<and> (Suc j mod Suc (Suc 0)) = 1) \<or> ((j mod Suc (Suc 0)) = 1 \<and> (Suc j mod Suc (Suc 0)) = 0)"
  by(induct j, simp, metis One_nat_def Suc_1 mod2_Suc_Suc)

lemma j_mod2_cases':"(j mod Suc (Suc 0)) = 0 \<or> (j mod Suc (Suc 0)) = 1"
  apply(induct j, simp) 
  using j_mod2_cases by blast

lemma j_mod2_suc:"j mod Suc (Suc 0) = 0 \<Longrightarrow> Suc j mod Suc (Suc 0) = 1" by (metis j_mod2_cases)

lemma descentPathEx:"descentIpath (sconst One) (srepeat [h1, h1'])"
  unfolding descentIpath_iff_snth
  apply(rule exI[of _ 0], clarsimp)
  apply(intro conjI allI )
  subgoal for j by(rule disjE[OF j_mod2_cases[of j]], simp_all)
  subgoal for j 
    apply(rule disjE[OF j_mod2_cases[of j]])
    subgoal by(rule exI[of _ j], simp)
    subgoal by(rule exI[of _ "Suc j"], simp add: j_mod2_suc) . .

lemma pathConEx:"Graph.pathCon {One} (\<lambda>u v. True) One One"
  unfolding Graph.pathCon_def
  using Graph.pathG.Base[of One One "{One}" "(\<lambda>u v. True)"] by auto

lemma scsgEx:"scsg {One} (\<lambda>u v. True)"
  unfolding scsg_def apply safe
  subgoal unfolding subgr_def by (auto simp: edgeTrue)
  subgoal unfolding Graph.scg_def using pathConEx by auto .

(*Incomplete*)
proposition "InfiniteDescent"
  apply(rule InfiniteDescentI)
  apply(drule ipath_isOne)
  apply(rule exI[of _ "srepeat [h1, h1']"])
  using descentPathEx by auto

proposition "\<not>SDdescending"
  unfolding SDdescending_def apply safe
  apply(erule allE[of _ "{One}"])
  apply(elim allE[of _ "\<lambda>u v. True"] impE, simp add: scsgEx)
  apply(elim exE conjE)
  unfolding decreasingPCC_def wfLabF_def apply clarify
  subgoal for lab nd nd' apply(cases nd, cases nd', simp)
    by(elim allE[of _ One], simp add: RR_defs) . 




end 
