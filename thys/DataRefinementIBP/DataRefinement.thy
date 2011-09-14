header {*  Data Refinement of Diagrams *}

theory DataRefinement
imports Diagram
begin

text{*
Next definition introduces the concept of data refinement of $(\mathit{assert} \  q)\circ (\mathit{demonic}\ Q)$
to $S$ using the data abstractions $R$ and $R'$.
*}

definition
  "DataRefinement p Q R R' S = (\<forall> s . \<Turnstile> {s' . s \<in> R s' \<and> s \<in> p} {| S |} (angelic R' (Q s)))"

text{*
The definition of the data refinement above is justified by the follwing two theorems.
*}

theorem datarefinement1:
  "mono S \<Longrightarrow> ((angelic R) o (assert p) o (demonic Q) \<le> S) = (\<forall> s . \<Turnstile> {s' . R s' s \<and> p s} {| S |} (Q s))"
  apply (simp add: le_fun_def assert_def angelic_def demonic_def Hoare_def le_bool_def)
  apply safe
  apply (simp_all add: Collect_def)
  apply auto
  apply (drule_tac x = "Q s" in spec)
  apply (drule_tac x = "x" in spec)
  apply auto
  apply (unfold simp_eq_emptyset)
  apply (drule_tac x = "s" in spec)
  apply auto
  apply (simp_all add: mem_def)
  apply (simp add: mono_def)
  by (metis rev_predicate1D)

theorem datarefinement2:
  "mono S \<Longrightarrow> ((angelic R) o (assert p) o (demonic Q) \<le> (S o (angelic R'))) = DataRefinement p Q R R' S"
  apply (simp_all add: datarefinement1 mono_comp)
  by (simp_all add: DataRefinement_def Hoare_def subset_eq mem_def)

text{*
If $\mathit{demonic}\ Q$ is correct with respect to $p$ and $q$, and $(\mathit{assert} \ p)\circ (\mathit{demonic}\  Q)$ 
is data refined
by $S$, then $S$ is correct with respect to $\mathit{angelic}\  R\  p$ and $\mathit{angelic} \ R' \ q$.
*}

theorem data_refinement:
  "mono S \<Longrightarrow> \<Turnstile> p {| demonic Q |} q \<Longrightarrow>  DataRefinement p Q R R' S \<Longrightarrow> 
         \<Turnstile> (angelic R p) {| S |} (angelic R' q)"
  apply (simp add: hoare_demonic DataRefinement_def angelic_def simp_eq_emptyset)
  apply (simp add: Hoare_def less_fun_def)
  apply safe
  apply (drule_tac x = "{s . R' s \<sqinter> Q xa \<noteq> \<bottom>}" and y = "{s . R' s \<sqinter> q \<noteq> \<bottom>}" in monoD)
  apply auto
  apply (drule_tac x = xa in spec)
  apply auto
  apply (unfold subset_eq)
  apply (unfold demonic_def)
  apply (erule notE)
  apply (rule antisym)
  apply auto
  apply (case_tac "R' xb \<sqinter> Q xa \<le> R' xb \<sqinter> q")
  apply simp
  apply (erule notE)
  apply (rule_tac inf_greatest)
  apply auto
  apply (rule_tac y = "Q xa" in order_trans)
  by auto


theorem data_refinement_choice:
  "DataRefinement p Q R R' S \<Longrightarrow> DataRefinement p Q R R' S' \<Longrightarrow> DataRefinement p Q R R' ( S \<sqinter> S') "
  by (simp add: DataRefinement_def hoare_choice)

theorem data_refinement_top [simp]:
  "DataRefinement p Q R R' \<top>"
  by (simp add: DataRefinement_def)


theorem data_refinement_choice2:
  "mono S \<Longrightarrow> mono S' \<Longrightarrow> DataRefinement p (Q::('a \<Rightarrow>'b::boolean_algebra)) R R' S \<Longrightarrow> DataRefinement p Q' R R' S' \<Longrightarrow> 
     DataRefinement p (Q \<squnion> Q') R R' ( S \<sqinter> S')"
  apply (simp add: DataRefinement_def sup_fun_def)
  apply (simp add: angelic_disjunctive hoare_choice)
  apply safe
  apply (rule hoare_mono)
  apply auto
  apply (rule_tac S = S' and Q = "angelic R' (Q' s)" in  hoare_mono)
  by auto

theorem (in DiagramTermination) dgr_data_refinement:
  "dmono D \<Longrightarrow>
   (\<forall> w i j . \<Turnstile> P w i  {| demonic (Q (i, j)) |} SUP_L_P P (pair w i) j) \<Longrightarrow>
   (\<forall> w i j . DataRefinement (P w i) (Q (i,j)) (R i) (R j) (D (i, j))) \<Longrightarrow>
   
   \<Turnstile> (dangelic R (SUP P)) {| pt D |} ((dangelic R (SUP P)) \<sqinter> (-(grd (step D))))"

  apply (simp add: dangelic_udisjunctive)
  apply (rule hoare_diagram2)
  apply (simp_all add: dangelic_def)
  apply safe
  apply (unfold dangelic_udisjunctive2)
  apply (simp_all add: dangelic_def)
  apply (rule data_refinement)
  by auto

theorem (in DiagramTermination) dgr_data_refinement1:
  "dmono D \<Longrightarrow>
   (\<forall> w i j . \<Turnstile> P w i  {| demonic (Q (i, j)) |} SUP_L_P P (pair w i) j) \<Longrightarrow>
   (\<forall> i j . DataRefinement ((SUP P) i) (Q (i,j)) (R i) (R j) (D (i, j))) \<Longrightarrow>
   
   \<Turnstile> (dangelic R (SUP P)) {| pt D |} ((dangelic R (SUP P)) \<sqinter> (-(grd (step D))))"

  apply (simp add: dangelic_udisjunctive)
  apply (rule hoare_diagram2)
  apply (simp_all add: dangelic_def)
  apply safe
  apply (unfold dangelic_udisjunctive2)
  apply (simp_all add: dangelic_def)
  apply (rule data_refinement)
  apply auto
  apply (unfold DataRefinement_def)
  apply safe
  apply (rule_tac P = "{s' . s \<in> R i s' \<and> s \<in> SUP P i}" in hoare_pre)
  apply auto
  apply (simp add: SUP_def Sup_fun_def Sup_bool_def mem_def)
  by auto

definition
  "DgrDataRefinement P T R D = (\<forall> i j . DataRefinement (P i) (T (i,j)) (R i) (R j) (D (i, j)))"


theorem DataRefinement_mono:
  "q \<le> p \<Longrightarrow> DataRefinement p Q R R' S \<Longrightarrow> DataRefinement q Q R R' S"
  apply (simp add: DataRefinement_def)
  apply auto
  apply (drule_tac x = "s" in spec)
  apply (rule hoare_pre)
  by auto
  
theorem DgrDataRefinement_mono:
  "Q \<le> P \<Longrightarrow> DgrDataRefinement P T R S \<Longrightarrow> DgrDataRefinement Q T R S"
  apply (simp add: DgrDataRefinement_def)
  apply auto
  apply (rule_tac p = "P i" and q = "Q i" in DataRefinement_mono)
  by (simp_all add: le_fun_def mem_def le_bool_def)

text{*
Next theorem is the diagram version of the data refinement theorem. If the
diagram demonic choice $T$ is correct, and it is refined by $D$, then
$D$ is also correct. One important point in this theorem is that 
if the diagram demonic choice $T$ terminates, then $D$ also terminates.
*}
  

theorem (in DiagramTermination) Diagram_DataRefinement:
  "\<lbrakk> dmono D; \<turnstile> P {|dgr_demonic T|} Q; DgrDataRefinement P T R D \<rbrakk>  \<Longrightarrow>
      \<turnstile> dangelic R P {| D |} ((dangelic R P) \<sqinter> (-(grd (step D))))" 

  apply (unfold Hoare_dgr_def DgrDataRefinement_def dgr_demonic_def)
  apply auto
  apply (rule_tac x="\<lambda> w . dangelic R (X w)" in exI)
  apply safe
  apply (unfold dangelic_udisjunctive2)
  apply (simp add: dangelic_def)
  apply (rule_tac Q="T(i,j)" in data_refinement)
  apply auto
  apply (rule_tac p = "(SUP X i)" in DataRefinement_mono)
  apply (simp add: SUP_def Sup_fun_def mem_def)
  apply auto
  apply (simp add: Sup_bool_def mem_def)
  apply auto
  by (simp_all add: dangelic_udisjunctive)
end