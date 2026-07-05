(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

subsubsection "Descending Unicycles Example"
theory Descending_Unicycles_Example
  imports "../Criterion/All" 
begin

(*types*)
datatype node = Zero | One | Two | Three
datatype pos= p0 | p1 | p2 | p2' | p3 | p3'

(*Nodes, Edges, Positions and Relations between them*)
definition "Node \<equiv> {Zero, One, Two, Three}"

lemma Z_Node[simp]:"Zero \<in> Node" by(simp add: Node_def)
lemma O_Node[simp]:"One \<in> Node" by(simp add: Node_def)
lemma T_Node[simp]:"Two \<in> Node" by(simp add: Node_def)
lemma Th_Node[simp]:"Three \<in> Node" by(simp add: Node_def)


lemma alw_nodes:"alw (holdsS Node) nds" 
  unfolding alw_holdsS_iff_snth Node_def apply(rule allI)
  subgoal for i apply(induct i)
    using node.exhaust by auto .
    

fun edge::"node \<Rightarrow> node \<Rightarrow> bool" where
"edge Zero One = HOL.True"|
"edge One Zero = HOL.True"|
"edge Zero Two = HOL.True"|
"edge Two Three = HOL.True"|
"edge Three Two = HOL.True"|
"edge _ _ = HOL.False"


lemma edge_into_zero[simp]:"edge nd Zero \<longleftrightarrow> nd = One" by(cases nd, auto)
lemma edge_into_one[simp]:"edge nd One \<longleftrightarrow> nd = Zero" by(cases nd, auto)
lemma edge_into_three[simp]:"edge nd Three \<longleftrightarrow> nd = Two" by(cases nd, auto)
lemma edge_three_into[simp]:"edge Three nd \<longleftrightarrow> nd = Two" by(cases nd, auto)
lemma edge_two_into[simp]:"edge Two nd \<longleftrightarrow> nd = Three" by(cases nd, auto)
lemma edge_zero_into[simp]:"edge Zero nd \<longleftrightarrow> nd = One \<or> nd = Two" by(cases nd, auto)


fun PosOf::"node \<Rightarrow> pos set" where 
"PosOf Zero = {p0}"|
"PosOf One = {p1}"|
"PosOf Two = {p2,p2'}"|
"PosOf Three = {p3,p3'}"


(*sets relating positions together*)
definition RR_set :: "((node \<times> pos) \<times> (node \<times> pos) \<times> slope) set" where
  "RR_set = {
     ((Zero, p0), (One, p1), Decr),

     ((One, p1), (Zero, p0), Main),

     ((Zero, p0), (Two, p2), Main),
     ((Zero, p0), (Two, p2'), Main),

     ((Two, p2), (Three, p3), Main),
     ((Two, p2'), (Three, p3'), Main),

     ((Three, p3), (Two, p2), Decr),
     
     ((Three, p3'), (Two, p2'), Main)
   }"


definition RR :: "node \<times> pos \<Rightarrow> node \<times> pos \<Rightarrow> slope \<Rightarrow> bool" where
  "RR np1 np2 s \<equiv> ((np1, np2, s) \<in> RR_set)"

lemmas RR_defs = RR_def RR_set_def

lemma RR_ZO[simp]:"RR (Zero, p0) (node.One, p1) Decr" unfolding RR_defs by auto
lemma RR_OZ[simp]:"RR (node.One, p1) (Zero, p0) Main" unfolding RR_defs by auto

lemma RR_TTr[simp]:"RR (Two, p2) (Three, p3) Main" unfolding RR_defs by auto
lemma RR_TrT[simp]:"RR (Three, p3) (Two, p2) Decr" unfolding RR_defs by auto

(*RR sound*)
lemma P_inPosOf:"RR (nd, P) (nd', P') sl \<Longrightarrow> P \<in> PosOf nd"
                 "RR (nd, P) (nd', P') sl \<Longrightarrow> P' \<in> PosOf nd'" by(auto simp: RR_defs)

interpretation Sloped_Graph where 
    Node = Node and edge = edge and PosOf = PosOf
    and RR = RR apply standard
  subgoal by(simp add: Node_def)
  subgoal by(unfold Node_def, auto elim: PosOf.cases)
  by(auto simp: RR_defs SlopedRels_def Node_def)

lemma notTZ:"\<not>pathG [node.Two, Zero]" by(rule notI, cases rule: pathG.cases[of "[node.Two, Zero]"], auto)
lemma notTO:"\<not>pathG [node.Two, One]" by(rule notI, cases rule: pathG.cases[of "[node.Two, One]"], auto)
lemma notTrZ:"\<not>pathG [node.Three, Zero]" by(rule notI, cases rule: pathG.cases[of "[node.Three, Zero]"], auto)
lemma notTrO:"\<not>pathG [node.Three, One]" by(rule notI, cases rule: pathG.cases[of "[node.Three, One]"], auto)
lemma notOT:"\<not>pathG [node.One, node.Two]" by(rule notI, cases rule: pathG.cases[of "[node.One, node.Two]"], auto)
lemma notOTr:"\<not>pathG [node.One, node.Three]" by(rule notI, cases rule: pathG.cases[of "[node.One, node.Three]"], auto)
lemma notZTr:"\<not>pathG [Zero, node.Three]" by(rule notI, cases rule: pathG.cases[of "[Zero, node.Three]"], auto)
lemma notZTZ:"\<not>pathG ([Zero,node.Two, Zero])"by(rule notI, cases rule: pathG.cases[of "[Zero,node.Two, Zero]"], auto)


lemma pathNWF_Three:"pathG p \<Longrightarrow> hd p = Three \<Longrightarrow> last p \<noteq> Zero \<and> last p \<noteq> One"
  apply(induct rule: pathG.induct)
  subgoal by auto
  subgoal for nd ndl apply (cases ndl, simp)
    subgoal for l ls by(cases "last ndl", simp_all split: if_splits) . .

lemma pathNWF_Two:"pathG p \<Longrightarrow> hd p = Two \<Longrightarrow> last p \<noteq> Zero \<and> last p \<noteq> One"
  apply(induct rule: pathG.induct)
  subgoal by auto
  subgoal for nd ndl apply (cases ndl, simp)
    subgoal for l ls by(cases "last ndl", simp_all split: if_splits) . .

lemma pathNWF_disj:"pathG pa \<Longrightarrow>
          hd pa = node.Two \<or> hd pa = node.Three \<Longrightarrow>
          last pa = Zero \<or> last pa = node.One \<Longrightarrow> HOL.False"
  apply(elim disjE) using pathNWF_Two pathNWF_Three by auto

(*Flat edges*)
lemma ZZ_FlatEdge:"\<not>(Zero, Zero) \<in> FlatEdges" unfolding FlatEdges_def by (simp add: RR_defs)
lemma OO_FlatEdge:"\<not>(One, One) \<in> FlatEdges" unfolding FlatEdges_def by (simp add: RR_defs)
lemma TT_FlatEdge:"\<not>(Two, Two) \<in> FlatEdges" unfolding FlatEdges_def by (simp add: RR_defs)
lemma ThTh_FlatEdge:"\<not>(Three, Three) \<in> FlatEdges" unfolding FlatEdges_def by (simp add: RR_defs)
lemmas same_FlatEdge = ZZ_FlatEdge OO_FlatEdge TT_FlatEdge ThTh_FlatEdge


lemma ZO_FlatEdge:"\<not>(Zero, One) \<in> FlatEdges" unfolding FlatEdges_def by (simp add: RR_defs)
lemma ThT_FlatEdge:"\<not>(Three, Two) \<in> FlatEdges" unfolding FlatEdges_def by (simp add: RR_defs)

lemma aux_ls:"xs \<noteq> [] \<Longrightarrow> (xs @ [Zero]) ! Suc 0 = node.Three \<Longrightarrow> length xs > 1" by(induct xs, auto) 

(*This graph doesn't have a flat cycle*)
theorem "\<not>FlatCycle"
  apply(rule notFlatCycleI,frule cycleG_shape, elim exE disjE)
  subgoal for _ x using same_FlatEdge by(cases x, auto)
  subgoal for nds x xs apply(cases x)
    (*cycle 0 ... 0*)
    subgoal using path_nth_edge[of "Zero # xs @ [Zero]" 0]
      apply(cases "xs ! 0")
      subgoal by (auto simp add: cycleG_def)
      subgoal by(erule allE[of _ 0], auto simp add: cycleG_def ZO_FlatEdge)
      subgoal using pathNWF_Two[of "xs @ [Zero]"] 
                    pathG_tl[of "xs @ [Zero]" Zero] 
                    hd_conv_nth[of xs] by (auto simp add: cycleG_def)
      subgoal by (auto simp add: cycleG_def) .
    (*cycle 1 ... 1*)
    subgoal apply(erule allE[of _ "length nds - 2"])
      using path_nth_edge[of "One # xs @ [One]" "length nds - 2"] 
      by (simp add: cycleG_def ZO_FlatEdge)
    (*cycle 2 ... 2*)
    subgoal apply(erule allE[of _ 1])
      using path_nth_edge[of "Two # xs @ [Two]" 0]
      using path_nth_edge[of "Two # xs @ [Two]" 1] 
      by (simp add: cycleG_def ThT_FlatEdge)
    (*cycle 3 ... 3*)
    subgoal apply(erule allE[of _ 0])
      using path_nth_edge[of "Three # xs @ [Three]" 0] 
      by (simp add: cycleG_def ThT_FlatEdge) . .



(*But is a descending cycle*)
lemma i_disj:"i < Suc (Suc (Suc 0)) \<longleftrightarrow> i = 0 \<or> i = 1 \<or> i = 2" by auto

lemma i_disj':"i < Suc (Suc 0) \<longleftrightarrow> i = 0 \<or> i = 1" by auto





lemma allCycles:"basicCycle c \<longleftrightarrow> c = [Zero, One, Zero] \<or> c = [One, Zero, One] \<or> c = [Two, Three, Two] \<or> c = [Three, Two, Three]"
apply(standard)
  subgoal unfolding basicCycle_def[unfolded cycleG_def] apply(elim conjE)
    apply(cases rule: pathG.cases[of c], simp)
    subgoal for nd by(cases nd, auto)
    subgoal for nd'' ndl
      apply(cases ndl, simp)
      subgoal for nd ndl' apply(cases ndl', simp)
        subgoal for nd' ls
          apply(cases ls)
          subgoal apply(cases nd)
            subgoal by(cases nd', auto)
            subgoal by(cases nd', auto)
            subgoal by(cases nd', auto simp: notTZ)
            subgoal by(cases nd', auto simp: notTZ) .
          (*impossible cases*)
          subgoal for nnd ls' apply(cases nd)
              (**)
              subgoal apply(cases nd')
                subgoal by(cases nnd,cases nd'', auto)
                subgoal by(cases nnd,cases nd'', auto simp: notPathG_within' notOTr notOT)
                subgoal apply(cases nnd,cases nd'', auto simp: notPathG_within' notTO)
                  by (smt (verit, ccfv_threshold) PosOf.cases
                      butlast.simps(2) edge.elims(2) hd_last_singletonI
                      last.simps list.distinct(1) list.set_sel(1)
                      node.distinct(9) node.simps(4,6) pathG.cases
                      snoc_eq_iff_butlast)

                subgoal apply(cases nnd,cases nd'', auto simp: notPathG_within' notTrO notOT) using notZTr path_appendL[of "[Zero, Three]"] by auto . 
              (**)
              subgoal apply(cases nd')
                subgoal by(cases nnd,cases nd'', auto simp: notPathG_within' notZTr, (metis List.last_in_set edge.elims(2) node.distinct(9) node.simps(4,8)))
                subgoal by(cases nnd,cases nd'', auto)
                subgoal by(cases nnd,cases nd'', auto simp: notPathG_within' notTZ,metis append_Cons empty_append_eq_id notOT notPathG_within)
                subgoal apply(cases nnd,cases nd'', auto simp: notPathG_within' notTrZ,metis append_Cons empty_append_eq_id notOTr notPathG_within) . .
              (**)
              subgoal apply(cases nd')
                subgoal apply(cases nnd,cases nd'', auto) using notTZ path_appendL[of "[Two, Zero]"] by auto
                subgoal apply(cases nnd,cases nd'', auto) using notTO path_appendL[of "[Two, One]"] by auto
                subgoal by(cases nnd,cases nd'', auto simp: notPathG_within' notTZ)
                subgoal by(cases nnd,cases nd'', auto simp: notTrO notTrZ notPathG_within') .
              (**)
              subgoal apply(cases nd')
                subgoal apply(cases nnd,cases nd'', auto) using notTrZ path_appendL[of "[Three, Zero]"] by auto
                subgoal apply(cases nnd,cases nd'', auto) using notTrO path_appendL[of "[Three, One]"] by auto
                subgoal by(cases nnd,cases nd'', auto simp: notTZ notTO notPathG_within')
                subgoal by(cases nnd,cases nd'', auto simp: notTrZ notTrO notPathG_within') . . . . . .
                 
  subgoal apply(elim disjE, simp_all add: basicCycle_def cycleG_def)
    subgoal unfolding ls_app by(rule pathG.Step, auto simp: pathG.Base)
    subgoal unfolding ls_app by(rule pathG.Step, auto simp: pathG.Base)
    subgoal unfolding ls_app by(rule pathG.Step, auto simp: pathG.Base)
    subgoal unfolding ls_app by(rule pathG.Step, auto simp: pathG.Base) . .


lemma notConnectedCyclesI:"(\<And>p. pathG p \<Longrightarrow> hd p \<in> set c' \<Longrightarrow> last p \<in> set c \<Longrightarrow> HOL.False) \<Longrightarrow>\<not> connectedCycles c' c"
unfolding connectedCycles_def by auto

lemma unicycle:"unicyclesGraph"
  apply(rule unicyclesGraphI', unfold allCycles connectedCycles_def, elim exE conjE disjE)
  subgoal by simp 
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  subgoal using pathNWF_disj by auto
  by auto 

lemma SDG:"SimplyDescendingGraph"
  apply(rule SimplyDescendingGraphI', unfold allCycles cycleDescends_def, elim disjE)
  (*0,1,0*)
  subgoal for c apply(intro exI[of _ 1] exI[of _ "[p0,p1,p0]"] conjI, simp_all)
    subgoal unfolding wfLabL_def by (clarsimp, unfold i_disj, force)
    subgoal unfolding descentPath_def by(clarsimp, unfold i_disj', force) .
  (*1,0,1*)
  subgoal for c apply(intro exI[of _ 1] exI[of _ "[p1,p0,p1]"] conjI, simp_all)
    subgoal unfolding wfLabL_def by (clarsimp, unfold i_disj, force)
    subgoal unfolding descentPath_def by(clarsimp, unfold i_disj', force) .
  (*2,3,2*)
  subgoal for c apply(intro exI[of _ 1] exI[of _ "[p2,p3,p2]"] conjI, simp_all)
    subgoal unfolding wfLabL_def by (clarsimp, unfold i_disj, force)
    subgoal unfolding descentPath_def by(clarsimp, unfold i_disj', force) .
  (*3,2,3*)
  subgoal for c apply(intro exI[of _ 1] exI[of _ "[p3,p2,p3]"] conjI, simp_all)
    subgoal unfolding wfLabL_def by (clarsimp, unfold i_disj, force)
    subgoal unfolding descentPath_def by(clarsimp, unfold i_disj', force) . .

theorem InfiniteDescent
  apply(unfold DescendingUnicyclesCriterion[OF unicycle])
  using SDG by auto

end
