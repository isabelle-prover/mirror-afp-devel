theory Context_Compatible_Order
  imports
    Ground_Context
    Restricted_Order
begin

locale restriction_restricted =  
  fixes restriction context_restriction restricted restricted_context
  assumes
    restricted:
      "\<And>t. t \<in> restriction \<longleftrightarrow> restricted t"
      "\<And>c. c \<in> context_restriction \<longleftrightarrow> restricted_context c"

locale restricted_context_compatibility =
  restriction_restricted +
  fixes R Fun
  assumes
    context_compatible [simp]:
      "\<And>c t\<^sub>1 t\<^sub>2.
        restricted t\<^sub>1 \<Longrightarrow>
        restricted t\<^sub>2 \<Longrightarrow>
        restricted_context c \<Longrightarrow>
        R (Fun\<langle>c;t\<^sub>1\<rangle>) (Fun\<langle>c;t\<^sub>2\<rangle>) \<longleftrightarrow> R t\<^sub>1 t\<^sub>2"

locale context_compatibility = restricted_context_compatibility where
  restriction = UNIV and context_restriction = UNIV and restricted = "\<lambda>_. True" and
  restricted_context = "\<lambda>_. True"
begin

lemma context_compatibility [simp]: "R (Fun\<langle>c;t\<^sub>1\<rangle>) (Fun\<langle>c;t\<^sub>2\<rangle>) \<longleftrightarrow> R t\<^sub>1 t\<^sub>2"
  by simp

end

locale context_compatible_restricted_order =
  restricted_total_strict_order +
  restriction_restricted +
  fixes Fun
  assumes less_context_compatible:
    "\<And>c t\<^sub>1 t\<^sub>2.
      restricted t\<^sub>1 \<Longrightarrow>
      restricted t\<^sub>2 \<Longrightarrow>
      restricted_context c \<Longrightarrow>
      t\<^sub>1 \<prec> t\<^sub>2 \<Longrightarrow>
      Fun\<langle>c;t\<^sub>1\<rangle> \<prec> Fun\<langle>c;t\<^sub>2\<rangle>"
begin

sublocale restricted_context_compatibility where R = "(\<prec>)"
  using less_context_compatible restricted
  by unfold_locales (metis dual_order.asym totalp totalp_onD)

sublocale less_eq: restricted_context_compatibility where R = "(\<preceq>)"
  using context_compatible restricted_not_le dual_order.order_iff_strict restricted
  by unfold_locales metis

lemma context_less_term_lesseq:
  assumes
    "restricted t"
    "restricted t'"
    "restricted_context c"
    "restricted_context c'"
    "\<And>t. restricted t \<Longrightarrow> Fun\<langle>c;t\<rangle> \<prec> Fun\<langle>c';t\<rangle>"
    "t \<preceq> t'"
  shows "Fun\<langle>c;t\<rangle> \<prec> Fun\<langle>c';t'\<rangle>"
  using assms context_compatible dual_order.strict_trans
  by blast

lemma context_lesseq_term_less:
  assumes
    "restricted t"
    "restricted t'"
    "restricted_context c"
    "restricted_context c'"
    "\<And>t. restricted t \<Longrightarrow> Fun\<langle>c;t\<rangle> \<preceq> Fun\<langle>c';t\<rangle>"
    "t \<prec> t'"
  shows "Fun\<langle>c;t\<rangle> \<prec> Fun\<langle>c';t'\<rangle>"
  using assms context_compatible dual_order.strict_trans1
  by meson

end

locale context_compatible_order =
  total_strict_order +
  fixes Fun
  assumes less_context_compatible: "t\<^sub>1 \<prec> t\<^sub>2 \<Longrightarrow> Fun\<langle>c;t\<^sub>1\<rangle> \<prec> Fun\<langle>c;t\<^sub>2\<rangle>"
begin

sublocale restricted: context_compatible_restricted_order where
  restriction = UNIV and context_restriction = UNIV and restricted = "\<lambda>_. True" and
  restricted_context = "\<lambda>_. True"
  using less_context_compatible
  by unfold_locales simp_all

sublocale context_compatibility "(\<prec>)"
  by unfold_locales

sublocale less_eq: context_compatibility "(\<preceq>)"
  by unfold_locales

lemma context_less_term_lesseq:
  assumes
   "\<And>t. Fun\<langle>c;t\<rangle> \<prec> Fun\<langle>c';t\<rangle>"
    "t \<preceq> t'"
  shows "Fun\<langle>c;t\<rangle> \<prec> Fun\<langle>c';t'\<rangle>"
  using assms restricted.context_less_term_lesseq
  by blast

lemma context_lesseq_term_less:
  assumes
    "\<And>t. Fun\<langle>c;t\<rangle> \<preceq> Fun\<langle>c';t\<rangle>"
    "t \<prec> t'"
  shows "Fun\<langle>c;t\<rangle> \<prec> Fun\<langle>c';t'\<rangle>"
  using assms restricted.context_lesseq_term_less
  by blast

end

end
