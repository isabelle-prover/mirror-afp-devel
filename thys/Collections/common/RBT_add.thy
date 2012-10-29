(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Additions to RB-Trees} *}
theory RBT_add
imports "~~/src/HOL/Library/RBT" "../iterator/SetIteratorOperations"
begin
text_raw {*\label{thy:RBT_add}*}

lemma tlt_trans: "\<lbrakk>l |\<guillemotleft> u; u\<le>v\<rbrakk> \<Longrightarrow> l |\<guillemotleft> v"
  by (induct l) auto

lemma trt_trans: "\<lbrakk> u\<le>v; v\<guillemotleft>|r \<rbrakk> \<Longrightarrow> u\<guillemotleft>|r"
  by (induct r) auto

lemmas tlt_trans' = tlt_trans[OF _ less_imp_le]
lemmas trt_trans' = trt_trans[OF less_imp_le]

fun rm_iterateoi 
  :: "('k,'v) RBT_Impl.rbt \<Rightarrow> ('k \<times> 'v, '\<sigma>) set_iterator"
  where
  "rm_iterateoi RBT_Impl.Empty c f \<sigma> = \<sigma>" |
  "rm_iterateoi (RBT_Impl.Branch col l k v r) c f \<sigma> = (
    if (c \<sigma>) then
      let \<sigma>' = rm_iterateoi l c f \<sigma> in
        if (c \<sigma>') then
          rm_iterateoi r c f (f (k, v) \<sigma>')
        else \<sigma>'
    else 
      \<sigma>
  )"

lemma rm_iterateoi_abort :
  "\<not>(c \<sigma>) \<Longrightarrow> rm_iterateoi t c f \<sigma> = \<sigma>"
by (cases t) auto

lemma rm_iterateoi_alt_def :
  "rm_iterateoi RBT_Impl.Empty = set_iterator_emp"
  "rm_iterateoi (RBT_Impl.Branch col l k v r) = 
   set_iterator_union (rm_iterateoi l)
     (set_iterator_union (set_iterator_sng (k, v)) (rm_iterateoi r))"
by (simp_all add: fun_eq_iff set_iterator_emp_def rm_iterateoi_abort
                  set_iterator_union_def set_iterator_sng_def Let_def)
declare rm_iterateoi.simps[simp del]


fun rm_reverse_iterateoi 
  :: "('k,'v) RBT_Impl.rbt \<Rightarrow> ('k \<times> 'v, '\<sigma>) set_iterator"
  where
  "rm_reverse_iterateoi RBT_Impl.Empty c f \<sigma> = \<sigma>" |
  "rm_reverse_iterateoi (Branch col l k v r) c f \<sigma> = (
    if (c \<sigma>) then
      let \<sigma>' = rm_reverse_iterateoi r c f \<sigma> in
        if (c \<sigma>') then
          rm_reverse_iterateoi l c f (f (k, v) \<sigma>')
        else \<sigma>'
    else 
      \<sigma>
  )"

lemma rm_reverse_iterateoi_abort :
  "\<not>(c \<sigma>) \<Longrightarrow> rm_reverse_iterateoi t c f \<sigma> = \<sigma>"
by (cases t) auto

lemma rm_reverse_iterateoi_alt_def :
  "rm_reverse_iterateoi RBT_Impl.Empty = set_iterator_emp"
  "rm_reverse_iterateoi (RBT_Impl.Branch col l k v r) = 
   set_iterator_union (rm_reverse_iterateoi r)
     (set_iterator_union (set_iterator_sng (k, v)) (rm_reverse_iterateoi l))"
by (simp_all add: fun_eq_iff set_iterator_emp_def rm_reverse_iterateoi_abort
                  set_iterator_union_def set_iterator_sng_def Let_def)
declare rm_reverse_iterateoi.simps[simp del]


lemma finite_dom_lookup [simp, intro!]: "finite (dom (RBT.lookup t))"
by(simp add: RBT.lookup_def)

instantiation rbt :: ("{equal, linorder}", equal) equal begin

definition "equal_class.equal (r :: ('a, 'b) rbt) r' == RBT.impl_of r = RBT.impl_of r'"

instance
proof
qed (simp add: equal_rbt_def RBT.impl_of_inject)

end

hide_const (open) impl_of lookup empty insert delete
  entries keys bulkload map_entry map fold

end
