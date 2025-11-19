section \<open>Rewriting\<close>

theory Rewriting
  imports Regular_Tree_Relations.Term_Context
    Regular_Tree_Relations.Ground_Terms
    Utils
    First_Order_Rewriting.Trs
    First_Order_Rewriting.Parallel_Rewriting
begin

subsection \<open>Ground variants connecting to FORT\<close>

definition grrstep :: "('f, 'v) trs \<Rightarrow> 'f gterm rel" where
  "grrstep \<R> = inv_image (rrstep \<R>) term_of_gterm"

definition gnrrstep :: "('f, 'v) trs \<Rightarrow> 'f gterm rel" where
  "gnrrstep \<R> = inv_image (nrrstep \<R>) term_of_gterm"

definition grstep :: "('f, 'v) trs \<Rightarrow> 'f gterm rel" where
  "grstep \<R> = inv_image (rstep \<R>) term_of_gterm"

definition gpar_rstep :: "('f, 'v) trs \<Rightarrow> 'f gterm rel" where
  "gpar_rstep \<R> = inv_image (par_rstep \<R>) term_of_gterm"


text \<open>
  An alternative induction scheme that treats the rule-case, the
  substition-case, and the context-case separately.
\<close>


abbreviation "linear_sys \<R> \<equiv> (\<forall> (l, r) \<in> \<R>. linear_term l \<and> linear_term r)"
abbreviation "const_subt c \<equiv> \<lambda> x. Fun c []"



end