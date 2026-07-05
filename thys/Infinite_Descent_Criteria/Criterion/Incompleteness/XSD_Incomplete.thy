(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)
subsection "Extended Sprenger-Dam Criterion Incompleteness"

theory XSD_Incomplete
imports "../Incomplete_Criteria"
begin


(* EXTENDED SPRENGER-DAM INCOMPLETE *)
(*A counter example to show incompleteness*)
(*types*)
datatype node = One | Two | Three
datatype pos = p1 | p1' | p2 | p3

(*Nodes, Edges, Positions and Relations between them*)
definition "Node \<equiv> {One, Two, Three}"

  
lemma nd_notOne:"nd \<noteq> One \<longleftrightarrow> nd = Two \<or> nd = Three" by(cases nd, auto)

lemma O_Node[simp]:"One \<in> Node" by(simp add: Node_def)
lemma T_Node[simp]:"Two \<in> Node" by(simp add: Node_def)
lemma Tr_Node[simp]:"Three \<in> Node" by(simp add: Node_def)

lemma alw_nodes:"alw (holdsS Node) nds" 
  unfolding alw_holdsS_iff_snth Node_def apply(rule allI)
  subgoal for i apply(induct i)
    using node.exhaust by auto .
    

fun edge::"node \<Rightarrow> node \<Rightarrow> bool" where
"edge One Two = HOL.True"|
"edge Two One = HOL.True"|
"edge One Three = HOL.True"|
"edge Three One = HOL.True"|
"edge _ _ = HOL.False"


fun PosOf::"node \<Rightarrow> pos set" where 
"PosOf One = {p1, p1'}"|
"PosOf Two = {p2}"|
"PosOf Three = {p3}"


(*sets relating positions together*)
definition RR_set :: "((node \<times> pos) \<times> (node \<times> pos) \<times> slope) set" where
  "RR_set = {
     ((One, p1), (Two, p2), Main),
     ((Two, p2), (One, p1), Decr),
     ((Two, p2), (One, p1'), Decr),
     ((One, p1'), (Three, p3), Main),
     ((Three, p3), (One, p1'), Decr),
     ((Three, p3), (One, p1), Decr)
 }"

definition EE_set :: "((node \<times> pos) \<times> (node \<times> pos)) set" where
  "EE_set = {
     ((One, p1), (Two, p2)),
     ((Two, p2), (One, p1)),
     ((Two, p2), (One, p1')),
     ((One, p1'), (Three, p3)),
     ((Three, p3), (One, p1')),
     ((Three, p3), (One, p1))
 }"


definition EE :: "node \<times> pos \<Rightarrow> node \<times> pos \<Rightarrow> bool" where
  "EE np1 np2 \<equiv> ((np1, np2) \<in> EE_set)"

lemmas EE_defs = EE_def EE_set_def


definition RR :: "node \<times> pos \<Rightarrow> node \<times> pos \<Rightarrow> slope \<Rightarrow> bool" where
  "RR np1 np2 s \<equiv> ((np1, np2, s) \<in> RR_set)"

lemmas RR_defs = RR_def RR_set_def

lemma RR_OT[simp]:"RR (One, p1) (Two, p2) Main" unfolding RR_defs by auto
lemma RR_TO[simp]:"RR (Two, p2) (One, p1) Decr" unfolding RR_defs by auto
lemma RR_TO'[simp]:"RR (Two, p2) (One, p1') Decr" unfolding RR_defs by auto
lemma RR_OTr[simp]:"RR (One, p1') (Three, p3) Main" unfolding RR_defs by auto
lemma RR_TrO[simp]:"RR (Three, p3) (One, p1') Decr" unfolding RR_defs by auto
lemma RR_TrO'[simp]:"RR (Three, p3) (One, p1) Decr" unfolding RR_defs by auto

(*RR sound*)
lemma P_inPosOf:"RR (nd, P) (nd', P') sl \<Longrightarrow> P \<in> PosOf nd"
                 "RR (nd, P) (nd', P') sl \<Longrightarrow> P' \<in> PosOf nd'" by(auto simp: RR_defs)

interpretation Sloped_Graph where 
    Node = Node and edge = edge and PosOf = PosOf
    and RR = RR apply standard
  subgoal by(simp add: Node_def)
  subgoal by(unfold Node_def, auto elim: PosOf.cases)
  by(auto simp: RR_defs SlopedRels_def Node_def)

(* Type 1: Eventually only visits One and Two *)
definition ipath12 :: "node stream \<Rightarrow> bool" where
  "ipath12 s \<equiv> ev (alw (holds (\<lambda>n. n = One \<or> n = Two))) s"

(* Type 2: Eventually only visits One and Three *)
definition ipath13 :: "node stream \<Rightarrow> bool" where
  "ipath13 s \<equiv> ev (alw (holds (\<lambda>n. n = One \<or> n = Three))) s"

(* Type 3: Vists both wings (Two and Three) infinitely often *)
definition ipath_mixed :: "node stream \<Rightarrow> bool" where
  "ipath_mixed s \<equiv> alw (ev (holds (\<lambda>n. n = Two))) s \<and> alw (ev (holds (\<lambda>n. n = Three))) s"

lemmas ipaths = ipath12_def ipath13_def ipath_mixed_def

(* The proof uses the fact that if a path does not eventually stay 
     in one wing, it must switch between them infinitely often. *)
lemma ipath_cases:"ipath nds \<Longrightarrow> ipath12 nds \<or> ipath13 nds \<or> ipath_mixed nds"
unfolding ipaths
  apply (cases "ev (alw (holds (\<lambda>n. n \<noteq> Three))) nds")
  apply (cases "ev (alw (holds (\<lambda>n. n \<noteq> Two))) nds")
    (* Case: Both nodes are eventually avoided (impossible for infinite ipath) *)
    subgoal unfolding ev_alw_holds_iff_snth alw_ev_holds_iff_snth by (meson PosOf.cases)
    (* Case: Eventually avoids Three but hits Two infinitely *)
    subgoal unfolding ev_alw_holds_iff_snth alw_ev_holds_iff_snth by (meson PosOf.cases)
    (* Case: Hits both infinitely *)
    subgoal unfolding ev_alw_holds_iff_snth alw_ev_holds_iff_snth by (meson PosOf.cases) .

lemma ipath_dist21:
  assumes "ipath nds"
  shows "nds !! i = Two \<Longrightarrow> nds !! Suc i = One"
  using assms unfolding ipath_def
  apply(induct i)
  apply(unfold alw_holds2_iff_snth)
  by(metis edge.elims(2) node.distinct(1))+

lemma ipath_dist31:
  assumes "ipath nds"
  shows "nds !! i = Three \<Longrightarrow> nds !! Suc i = One"
  using assms unfolding ipath_def
  apply(induct i)
  apply(unfold alw_holds2_iff_snth)
  by (metis edge.elims(2) edge.simps(7))+


lemma ipath_dist1:
  assumes "ipath nds"
  shows "nds !! i = One \<Longrightarrow> nds !! Suc i = Two \<or> nds !! Suc i = Three"
  using assms unfolding ipath_def
  apply(induct i)
  apply(unfold alw_holds2_iff_snth)
  by (metis edge.elims(2) edge.simps(7))+

(*These path types all descend*)
lemma ipath12_descent:
  assumes "ipath nds"
  shows "ipath12 nds \<Longrightarrow> \<exists>Ps. descentIpath nds Ps"
  unfolding ipaths ev_alw_holds_iff_snth
proof(erule exE)
  fix i
  assume assm:"\<forall>j\<ge>i. nds !! j = One \<or> nds !! j = Two"

  (* Define the witness position stream *)
  let ?Ps = "smap (\<lambda>n. if n = One then p1 else p2) nds"

  show ?thesis 
    apply (unfold descentIpath_def, intro exI[of _ ?Ps] sdrop_evI[of _ i] conjI)
    (*always RR*)
    subgoal unfolding alw_holds2_iff_snth
      apply (clarsimp split: if_splits prod.splits, intro conjI impI)
      subgoal for i' using ipath_dist1[OF assms, of "i' + i"] by (simp add: add.commute sdrop_snth)
      subgoal for i' using ipath_dist1[OF assms, of "i' + i"] 
        unfolding RR_defs
        by (auto simp add: add.commute sdrop_snth,metis assm le_Suc_eq le_add2 node.distinct(3,5))
      subgoal for i' unfolding nd_notOne RR_defs
        using ipath_dist21[OF assms, of "i' + i"] 
              ipath_dist31[OF assms, of "i' + i"]
        by (auto simp add: add.commute sdrop_snth,metis assm le_add2 node.distinct(3,5))
      subgoal for i' unfolding nd_notOne RR_defs
        using ipath_dist21[OF assms, of "i' + i"] 
              ipath_dist31[OF assms, of "i' + i"]
        by (auto simp add: add.commute sdrop_snth) .
      (*always eventually decreasing*)
    unfolding alw_ev_holds2_iff_snth
    apply(rule allI, simp)
    subgoal for i' 
      apply(cases "sdrop i nds !! i'")
      subgoal apply(rule exI[of _ "Suc i'"])
        using ipath_dist1[OF assms, of "i' + i"]
              ipath_dist21[OF assms, of "Suc (i' + i)"]
              ipath_dist31[OF assms, of "Suc (i' + i)"]
        by (auto simp add: add.commute sdrop_snth,metis assm less_add_Suc2 nat_less_le node.distinct(3,5))
      subgoal apply(rule exI[of _ i']) 
        using ipath_dist21[OF assms, of "i' + i"] 
        by (simp add: add.commute sdrop_snth)
      subgoal using assm by (metis le_add1 node.distinct(3,5) sdrop_snth) . .
qed

lemma ipath13_descent:
  assumes "ipath nds"
  shows "ipath13 nds \<Longrightarrow> \<exists>Ps. descentIpath nds Ps"
  unfolding ipaths ev_alw_holds_iff_snth
proof(erule exE)
  fix i
  assume assm:"\<forall>j\<ge>i. nds !! j = One \<or> nds !! j = Three"

  (* Define the witness position stream *)
  let ?Ps = "smap (\<lambda>n. if n = One then p1' else p3) nds"

  show ?thesis 
    apply (unfold descentIpath_def, intro exI[of _ ?Ps] sdrop_evI[of _ i] conjI)
    (*always RR*)
    subgoal unfolding alw_holds2_iff_snth 
      apply (clarsimp split: if_splits prod.splits, intro conjI impI)
      subgoal for i' using ipath_dist1[OF assms, of "i' + i"] by (simp add: add.commute sdrop_snth)
      subgoal for i' using ipath_dist1[OF assms, of "i' + i"] 
        unfolding RR_defs
        by (auto simp add: add.commute sdrop_snth, metis assm less_add_Suc2 less_or_eq_imp_le node.distinct(1,5))
      subgoal for i' unfolding nd_notOne RR_defs
        using ipath_dist21[OF assms, of "i' + i"] 
              ipath_dist31[OF assms, of "i' + i"]
        by (auto simp add: add.commute sdrop_snth, metis add.commute assm le_iff_add node.distinct(1,5))
      subgoal for i' unfolding nd_notOne RR_defs
        using ipath_dist21[OF assms, of "i' + i"] 
              ipath_dist31[OF assms, of "i' + i"]
        by (auto simp add: add.commute sdrop_snth) .
      (*always eventually decreasing*)
    unfolding alw_ev_holds2_iff_snth
    apply(rule allI, simp)
    subgoal for i' 
      apply(cases "sdrop i nds !! i'")
      subgoal apply(rule exI[of _ "Suc i'"])
        using ipath_dist1[OF assms, of "i' + i"]
              ipath_dist21[OF assms, of "Suc (i' + i)"]
              ipath_dist31[OF assms, of "Suc (i' + i)"]
        by (auto simp add: add.commute sdrop_snth, metis assm less_add_Suc2 nat_less_le node.distinct(1,5))
      subgoal by (metis le_add1 node.distinct(1,5) sdrop_snth assm)
      apply(rule exI[of _ i'])
        using ipath_dist31[OF assms, of "i' + i"] 
        by (simp add: add.commute sdrop_snth) .
qed


lemma ipath_mixed_descent:
  assumes "ipath nds"
  shows "ipath_mixed nds \<Longrightarrow> \<exists>Ps. descentIpath nds Ps"
unfolding ipaths alw_ev_holds_iff_snth
proof(elim conjE)
  assume assm:"\<forall>i. \<exists>j\<ge>i. nds !! j = Two"
              "\<forall>i. \<exists>j\<ge>i. nds !! j = Three"

  (* Define the witness position stream *)
  let ?Ps = "smap2 (\<lambda>n next_n. 
    if n = Two then p2
    else if n = Three then p3
    else if next_n = Two then p1
    else p1') nds (stl nds)"

  show ?thesis find_theorems sdrop 0
    apply (unfold descentIpath_def, intro exI[of _ ?Ps] sdrop_evI[of _ 0, unfolded sdrop.simps(1)] conjI)
    (*always RR*)
    subgoal unfolding alw_holds2_iff_snth 
      using ipath_dist31[OF assms] 
            ipath_dist21[OF assms] 
            ipath_dist1[OF assms]
      by (auto simp add: stl_Suc_eq,(metis PosOf.elims RR_OTr RR_OT)+)
    (*always eventually decreasing*)
    unfolding alw_ev_holds2_iff_snth
    apply(rule allI, simp add: RR_defs)
    using assm(2) assms ipath_dist31 by auto
qed


lemma pathConEx11:"Graph.pathCon {One,Two,Three} (\<lambda>u v. edge u v) One One"
  unfolding Graph.pathCon_def
  using Graph.pathG.Step[of One "{One,Two,Three}" "(\<lambda>u v. edge u v)" "[One, Two]"]
        Graph.pathG.Base[of One Two "{One,Two,Three}" "(\<lambda>u v. edge u v)"]
  by auto

lemma pathConEx12:"Graph.pathCon {One,Two,Three} (\<lambda>u v. edge u v) One Two"
  unfolding Graph.pathCon_def
  using Graph.pathG.Base[of One Two "{One,Two,Three}" "(\<lambda>u v. edge u v)"]
  by auto

lemma pathConEx13:"Graph.pathCon {One,Two,Three} (\<lambda>u v. edge u v) One Three"
  unfolding Graph.pathCon_def
  using Graph.pathG.Base[of One Three "{One,Two,Three}" "(\<lambda>u v. edge u v)"]
  by auto

lemma pathConEx21:"Graph.pathCon {One,Two,Three} (\<lambda>u v. edge u v) Two One"
  unfolding Graph.pathCon_def
  using Graph.pathG.Base[of Two One "{One,Two,Three}" "(\<lambda>u v. edge u v)"]
  by auto

lemma pathConEx31:"Graph.pathCon {One,Two,Three} (\<lambda>u v. edge u v) Three One"
  unfolding Graph.pathCon_def
  using Graph.pathG.Base[of Three One "{One,Two,Three}" "(\<lambda>u v. edge u v)"]
  by auto

lemma pathConEx23:"Graph.pathCon {One,Two,Three} (\<lambda>u v. edge u v) Two Three"
  using Graph.pathCon_trans[OF pathConEx21 pathConEx13] .

lemma pathConEx32:"Graph.pathCon {One,Two,Three} (\<lambda>u v. edge u v) Three Two"
  using Graph.pathCon_trans[OF pathConEx31 pathConEx12] .

lemmas pathConEx = pathConEx11 pathConEx12 
                   pathConEx13 pathConEx21 
                   pathConEx31 pathConEx23
                   pathConEx32

lemma scsgEx:"scsg {One,Two,Three} (\<lambda>u v. edge u v)"
  unfolding scsg_def apply safe
  subgoal unfolding subgr_def by (auto)
  subgoal unfolding Graph.scg_def using pathConEx 
    by (metis (full_types) Graph.pathCon_trans nd_notOne) .


lemma wfLabFSCases:
        "wfLabFS {One, Two, Three} lab \<Longrightarrow> 
        (lab One = {p1} \<or> lab One = {p1'} \<or> lab One = {p1,p1'}) \<and>
        lab Three = {p3} \<and> lab Two = {p2}" unfolding wfLabFS_def by auto

lemma noHCSC:"wfLabFS {One, Two, Three} lab \<Longrightarrow>
    RRSetChoice {One, Two, Three} edge lab f \<Longrightarrow> False"
  apply(drule wfLabFSCases, unfold RRSetChoice_def, safe)
  subgoal 
    apply(erule allE[of _ One], erule allE[of _ One])
    apply(erule allE[of _ Three], erule allE[of _ Three])
    by(auto simp: RR_defs)
  subgoal 
    apply(erule allE[of _ One], erule allE[of _ One])
    apply(erule allE[of _ Two], erule allE[of _ Two])
    by(auto simp: RR_defs)
  subgoal premises prem 
    using prem(1) prem(1) 
    apply-apply(erule allE[of _ One], erule allE[of _ One])
    apply-apply(erule allE[of _ Two], erule allE[of _ Three], simp add: prem)
    using prem(2,5) 
    apply-by(erule allE[of _ One], erule allE[of _ Three], simp add: RR_defs) .
    

(*Incomplete*)
proposition "InfiniteDescent"
  apply(rule InfiniteDescentI)
  apply(frule ipath_cases, elim disjE)
  subgoal using ipath12_descent by auto
  subgoal using ipath13_descent by auto
  subgoal using ipath_mixed_descent by auto .

proposition "\<not>XSDdescending"
  unfolding XSDdescending_def apply safe
  apply(erule allE[of _ "{One,Two,Three}"])
  apply(elim allE[of _ "\<lambda>u v. edge u v"] impE, simp add: scsgEx)
  apply(elim exE conjE)
  unfolding descending_PCSC_sliced_def  apply clarsimp
  subgoal for lab f using noHCSC[of lab f] by auto . 



end 
