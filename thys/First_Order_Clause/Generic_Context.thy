theory Generic_Context
  imports Context_Notation
begin

locale "context" =
  context_notation +
  assumes
    compose_context_iff [simp]: "\<And>(c :: 'c) c' (t :: 't). (c \<circ>\<^sub>c c')\<langle>t\<rangle> = c\<langle>c'\<langle>t\<rangle>\<rangle>" and
    apply_hole [simp]: "\<And>t. \<box>\<langle>t\<rangle> = t" and
    apply_context_eq [intro]: "\<And>c t t'. c\<langle>t\<rangle> = c\<langle>t'\<rangle> \<Longrightarrow> t = t'"

end
