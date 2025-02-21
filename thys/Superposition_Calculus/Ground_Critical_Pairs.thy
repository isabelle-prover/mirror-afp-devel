theory Ground_Critical_Pairs
  imports First_Order_Clause.Term_Rewrite_System
begin

definition ground_critical_pairs :: "'f gterm rel \<Rightarrow> 'f gterm rel" where
  "ground_critical_pairs R = {(ctxt\<langle>r\<^sub>2\<rangle>\<^sub>G, r\<^sub>1) | ctxt l r\<^sub>1 r\<^sub>2. (ctxt\<langle>l\<rangle>\<^sub>G, r\<^sub>1) \<in> R \<and> (l, r\<^sub>2) \<in> R}"

locale ground_critical_pair_theorem =
  fixes f_type :: "'f itself"
  assumes ground_critical_pair_theorem:
    "\<And>R :: 'f gterm rel.
      WCR (rewrite_inside_gctxt R) \<longleftrightarrow> ground_critical_pairs R \<subseteq> (rewrite_inside_gctxt R)\<^sup>\<down>"

end
