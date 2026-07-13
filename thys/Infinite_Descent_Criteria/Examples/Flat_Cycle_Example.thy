(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

subsubsection "Flat Cycle Counterexample"
theory Flat_Cycle_Example
  imports "../Criterion/All" 
begin


(*types*)
datatype node = Zero | One | Two
datatype pos= p0 | p0' | p1 | p1' | p2 | p2'

(*Nodes, Edges, Positions and Relations between them*)
definition "Node \<equiv> {Zero, One, Two}"

lemma Z_Node[simp]:"Zero \<in> Node" by(simp add: Node_def)
lemma T_Node[simp]:"Two \<in> Node" by(simp add: Node_def)
(*
lemma nd_aux[simp]:"nd \<noteq> Aux \<longleftrightarrow> nd = Flat" by(cases nd, auto)
lemma nd_flat[simp]:"nd \<noteq> Flat \<longleftrightarrow> nd = Aux" by(cases nd, auto)
*)

lemma alw_nodes:"alw (holdsS Node) nds" 
  unfolding alw_holdsS_iff_snth Node_def apply(rule allI)
  subgoal for i apply(induct i)
    using node.exhaust by auto .
    

fun edge::"node \<Rightarrow> node \<Rightarrow> bool" where
"edge Zero One = HOL.True"|
"edge One Zero = HOL.True"|
"edge Zero Two = HOL.True"|
"edge Two Zero = HOL.True"|
"edge _ _ = HOL.False"

fun PosOf::"node \<Rightarrow> pos set" where 
"PosOf Zero = {p0,p0'}"|
"PosOf One = {p1,p1'}"|
"PosOf Two = {p2,p2'}"


(*sets relating positions together*)
definition RR_set :: "((node \<times> pos) \<times> (node \<times> pos) \<times> slope) set" where
  "RR_set = {
     ((Zero, p0), (One, p1), Main),
     ((Zero, p0'), (One, p1'), Main),

     ((One, p1), (Zero, p0), Main),
     ((One, p1'), (Zero, p0'), Decr),

     ((Zero, p0), (Two, p2), Main),
     ((Zero, p0'), (Two, p2'), Main),

     ((Two, p2), (Zero, p0), Main),
     ((Two, p2'), (Zero, p0'), Main)
   }"


definition RR :: "node \<times> pos \<Rightarrow> node \<times> pos \<Rightarrow> slope \<Rightarrow> bool" where
  "RR np1 np2 s \<equiv> ((np1, np2, s) \<in> RR_set)"

lemmas RR_defs = RR_def RR_set_def

(*RR sound*)
lemma P_inPosOf:"RR (nd, P) (nd', P') sl \<Longrightarrow> P \<in> PosOf nd"
                 "RR (nd, P) (nd', P') sl \<Longrightarrow> P' \<in> PosOf nd'" by(auto simp: RR_defs)

interpretation Sloped_Graph where 
    Node = Node and edge = edge and PosOf = PosOf
    and RR = RR apply standard
  subgoal by(simp add: Node_def)
  subgoal by(unfold Node_def, auto elim: PosOf.cases)
  by(auto simp: RR_defs SlopedRels_def Node_def)

lemma listE:"(i < length ([Zero, node.Two] @ [Zero]) - 1) \<Longrightarrow> (i = 0 \<Longrightarrow> P) \<Longrightarrow> (i = 1 \<Longrightarrow> P) \<Longrightarrow> P" by fastforce

lemma ZT_FlatEdge:"(Zero, Two) \<in> FlatEdges" unfolding FlatEdges_def by (simp add: RR_defs)
lemma TZ_FlatEdge:"(Two, Zero) \<in> FlatEdges" unfolding FlatEdges_def by (simp add: RR_defs)

(*there exists a flat cycle between Zero and Two, so a contradiction to ID*)
lemma "\<not>InfiniteDescent"
  apply(rule Flat_Cycles_Criterion[unfolded FlatCycle_def])
  (*Choose our flat cycle*)
  apply(intro exI[of _ "([Zero,Two]) @ [Zero]"] conjI)
  (*Show they do indeed contain flat edges*)
  subgoal apply(intro allI impI, erule listE)
    using ZT_FlatEdge TZ_FlatEdge by auto
  (*Show it is a cycle*)
  subgoal unfolding cycleG_def 
    apply(rule conjI)
    subgoal by(rule pathG.Step, simp_all add: pathG.Base)
    by auto .


end
