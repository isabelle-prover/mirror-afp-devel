theory Heap
imports Terms "DistinctVars-Nominal" "Nominal-Utils"
begin

subsubsection {* Conversion from assignments to heaps *}

text {* The type @{typ assn} is the data type used in the let expression. It 
is isomorphic to @{typ "(var \<times> exp) list"}, but since Nominal does not
support nested data type, this redundancy was introduced. The following
function converts between them. Once Nominal supports nested data types, this
could be simplified. *}

nominal_primrec asToHeap :: "assn \<Rightarrow> heap" 
 where ANilToHeap: "asToHeap ANil = []"
 | AConsToHeap: "asToHeap (ACons v e as) = (v, e) # asToHeap as"
unfolding eqvt_def asToHeap_graph_aux_def
apply rule
apply simp
apply rule
apply(case_tac x rule: exp_assn.exhaust(2))
apply auto
done
termination(eqvt) by lexicographic_order

lemma asToHeap_eqvt: "eqvt asToHeap"
  unfolding eqvt_def
  by (auto simp add: permute_fun_def asToHeap.eqvt)

lemma set_bn_to_atom_heapVars:
  "set (bn as) = atom ` heapVars (asToHeap as)"
   apply (induct as rule: asToHeap.induct)
   apply (auto simp add: exp_assn.bn_defs)
   done

lemma fresh_assn_distinct:
 assumes "set (bn as) \<sharp>* \<Gamma>"
 shows "heapVars (asToHeap as) \<inter> heapVars \<Gamma> = {}"
 using assms
by (metis set_bn_to_atom_heapVars fresh_heapVars_distinct)

lemma distinctVars_append_asToHeap:
  assumes "distinctVars (asToHeap as)"
  assumes "distinctVars \<Gamma>"
  assumes "set (bn as) \<sharp>* \<Gamma>"
  shows "distinctVars (asToHeap as @ \<Gamma>)" 
by(rule distinctVars_appendI[OF assms(1,2) fresh_assn_distinct[OF assms(3)]])

end
