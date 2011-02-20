(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Additions to RB-Trees} *}
theory RBT_add
imports "~~/src/HOL/Library/RBT"
begin
text_raw {*\label{thy:RBT_add}*}

lemma tlt_trans: "\<lbrakk>l |\<guillemotleft> u; u\<le>v\<rbrakk> \<Longrightarrow> l |\<guillemotleft> v"
  by (induct l) auto

lemma trt_trans: "\<lbrakk> u\<le>v; v\<guillemotleft>|r \<rbrakk> \<Longrightarrow> u\<guillemotleft>|r"
  by (induct r) auto

lemmas tlt_trans' = tlt_trans[OF _ less_imp_le]
lemmas trt_trans' = trt_trans[OF less_imp_le]

fun rm_iterateoi 
  :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> ('k,'v) RBT_Impl.rbt \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
  where
  "rm_iterateoi c f RBT_Impl.Empty \<sigma> = \<sigma>" |
  "rm_iterateoi c f (RBT_Impl.Branch col l k v r) \<sigma> = (
    if (c \<sigma>) then
      let \<sigma>' = rm_iterateoi c f l \<sigma> in
        if (c \<sigma>') then
          rm_iterateoi c f r (f k v \<sigma>')
        else \<sigma>'
    else 
      \<sigma>
  )"

fun rm_reverse_iterateoi 
  :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> ('k,'v) RBT_Impl.rbt \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
  where
  "rm_reverse_iterateoi c f RBT_Impl.Empty \<sigma> = \<sigma>" |
  "rm_reverse_iterateoi c f (Branch col l k v r) \<sigma> = (
    if (c \<sigma>) then
      let \<sigma>' = rm_reverse_iterateoi c f r \<sigma> in
        if (c \<sigma>') then
          rm_reverse_iterateoi c f l (f k v \<sigma>')
        else \<sigma>'
    else 
      \<sigma>
  )"

lemma finite_dom_lookup [simp, intro!]: "finite (dom (RBT.lookup t))"
by(simp add: RBT.lookup_def)

instantiation rbt :: ("{equal, linorder}", equal) equal begin

definition "equal_class.equal (r :: ('a, 'b) rbt) r' == RBT.impl_of r = RBT.impl_of r'"

instance
proof
qed (simp add: equal_rbt_def impl_of_inject)

end

end
