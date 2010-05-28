header {*  Marking Using a Stack  *}

theory StackMark

imports SetMark DataRefinement

begin

text{*
In this theory we refine the set marking diagram to a diagram in which the
set is replaced by a list (stack). Iniatially the list contains the root element
and as long as the list is nonempty and the top of the list has an unmarked
successor $y$, then $y$ is added to the top of the list. If the top does not
have unmarked sucessors, it is removed from the list. The diagram terminates when
the list is empty.

The data refinement relation of the two diagrams is true if the list
has distinct elements and the elements of the list and the set are the same.
*}
consts
  "dist":: "'a list \<Rightarrow> bool";

primrec
  "dist []     = True"
  "dist (a # L)= (\<not> a mem L \<and> dist L)";

subsection {* Transitions *}

definition (in graph)
  "Q1' s \<equiv> let (stk::('node list), mrk::('node set)) = s in {(stk'::('node list), mrk') . 
           root = nil \<and> stk' = [] \<and> mrk' = mrk}";

definition (in graph)
  "Q2' s \<equiv> let (stk::('node list), mrk::('node set)) = s in {(stk', mrk') . root \<noteq> nil \<and> stk' = [root] \<and> mrk' = mrk \<union> {root}}";

definition (in graph)
  "Q3' s \<equiv> let (stk, mrk) = s in {(stk', mrk') .  stk \<noteq> [] \<and> (\<exists> y . (hd stk, y) \<in> next \<and> 
    y \<notin> mrk \<and> stk' = y # stk \<and> mrk' = mrk \<union> {y})}";

definition (in graph)
  "Q4' s \<equiv> let (stk, mrk) = s in {(stk', mrk') . stk \<noteq> [] \<and> 
  (\<forall> y . (hd stk, y) \<in> next \<longrightarrow> y \<in> mrk) \<and> stk' = tl stk \<and> mrk' = mrk}";

definition
  "Q5' s \<equiv> let (stk, mrk) = s in {(stk', mrk') . stk = [] \<and> mrk' = mrk}";

subsection {* Invariants *}

definition
  "Init' \<equiv> UNIV";

definition
  "Loop' \<equiv> { (stk, mrk) . dist stk}";

definition
  "Final' \<equiv> UNIV";

definition [simp]:
  "StackMarkInv i = (case i of
      I.init  \<Rightarrow> Init' |
      I.loop  \<Rightarrow> Loop' |
      I.final \<Rightarrow> Final')";

subsection {* Data refinement relations *}

definition
  "R1 \<equiv> \<lambda> (stk, mrk) . {(X, mrk') . mrk' = mrk}";

definition
  "R2 \<equiv> \<lambda> (stk, mrk) . {(X, mrk') . X = {x . x mem stk} \<and> (stk, mrk) \<in> Loop' \<and> mrk' = mrk}";

definition [simp]:
  "R i = (case i of
      I.init  \<Rightarrow> R1 |
      I.loop  \<Rightarrow> R2 |
      I.final \<Rightarrow> R1)";

definition (in graph)
  "StackMark_rel = (\<lambda> (i, j) . (case (i, j) of
      (I.init, I.loop)  \<Rightarrow> Q1' \<squnion> Q2' |
      (I.loop, I.loop)  \<Rightarrow> Q3' \<squnion> Q4' |
      (I.loop, I.final) \<Rightarrow> Q5' |
       _ \<Rightarrow> \<bottom>))";

subsection {* Data refinement of the transitions *}

theorem (in graph) init_nil [simp]:
  "DataRefinement Init Q1 R1 R2 (demonic Q1')";
   by (simp add: DataRefinement_def hoare_demonic Q1'_def Init_def 
     R1_def Loop'_def R1_def R2_def Q1_def angelic_def subset_eq);
   
theorem (in graph) init_root [simp]:
  "DataRefinement Init Q2 R1 R2 (demonic Q2')";
   by (simp add: DataRefinement_def hoare_demonic Q2'_def Init_def 
     R1_def Loop'_def R1_def R2_def Q2_def angelic_def subset_eq);

theorem (in graph) step1 [simp]:
  "DataRefinement Loop Q3 R2 R2 (demonic Q3')";
  apply (simp add: DataRefinement_def hoare_demonic Loop_def 
    Loop'_def R2_def Q3_def Q3'_def angelic_def subset_eq);
  apply (simp add: simp_eq_emptyset);
  apply clarify;
  apply (case_tac a);
  by auto;  

theorem (in graph) step2 [simp]:
  "DataRefinement Loop Q4 R2 R2 (demonic Q4')";
  apply (simp add: DataRefinement_def hoare_demonic Loop_def 
    Loop'_def R2_def Q4_def Q4'_def angelic_def subset_eq);
  apply (simp add: simp_eq_emptyset);
  apply clarify;
  apply (case_tac a);
  by auto;


theorem (in graph) final [simp]:
  "DataRefinement Loop Q5 R2 R1 (demonic Q5')";
  apply (simp add: DataRefinement_def hoare_demonic Loop_def 
    Loop'_def R2_def R1_def Q5_def Q5'_def angelic_def subset_eq);
  by (simp add: simp_eq_emptyset);

subsection {* Diagram data refinement *}

theorem (in graph) StackMark_DataRefinement [simp]:
 "DgrDataRefinement SetMarkInv SetMark_rel R (dgr_demonic StackMark_rel)";
  by (simp add: DgrDataRefinement_def dgr_demonic_def StackMark_rel_def SetMark_rel_def demonic_sup_inf SetMarkInv_def data_refinement_choice2);

subsection {* Diagram correctness *}

theorem (in graph) StackMark_correct:
  "Hoare_dgr (dangelic R SetMarkInv) (dgr_demonic StackMark_rel) ((dangelic R SetMarkInv) \<sqinter> (- grd (step ((dgr_demonic StackMark_rel)))))";
  apply (rule_tac T="SetMark_rel" in Diagram_DataRefinement);
  apply auto;
  by (rule SetMark_correct1);

end;