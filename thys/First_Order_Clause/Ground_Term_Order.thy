theory Ground_Term_Order
  imports
    Generic_Context
    Context_Compatible_Order
    Term_Order_Notation
    Transitive_Closure_Extra
begin

locale subterm_property =
  strict_order where less = less\<^sub>t +
  "context"
  for less\<^sub>t :: "'t \<Rightarrow> 't \<Rightarrow> bool" +
  assumes
    subterm_property [simp]: "\<And>t c. c \<noteq> \<box> \<Longrightarrow> less\<^sub>t t c\<langle>t\<rangle>"
begin

interpretation term_order_notation .

lemma less_eq_subterm_property: "t \<preceq>\<^sub>t c\<langle>t\<rangle>"
  using subterm_property
  by (metis apply_hole reflclp_iff)

end

locale ground_term_order =
  wellfounded_strict_order where less = less\<^sub>t +
  total_strict_order where less = less\<^sub>t +
  context_compatible_order where less = less\<^sub>t +
  subterm_property
begin

interpretation term_order_notation .

end

end
