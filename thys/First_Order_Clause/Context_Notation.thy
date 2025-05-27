theory Context_Notation
  imports Main
begin

locale apply_context_notation = 
  fixes apply_context :: "'c \<Rightarrow> 't \<Rightarrow> 't"
begin

notation apply_context (\<open>_\<langle>_\<rangle>\<close> [1000, 0] 1000)

end

locale Hole_notation = 
  fixes Hole :: "'c"
begin

notation Hole (\<open>\<box>\<close>)

end

locale compose_context_notation =
  fixes compose_context :: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
begin

notation compose_context (infixl \<open>\<circ>\<^sub>c\<close> 75)

end

locale subst_context_notation =
  fixes subst :: "'c \<Rightarrow> ('v \<Rightarrow> 't) \<Rightarrow> 'c"
begin

notation subst (infixl "\<cdot>t\<^sub>c" 67)

end

locale context_notation = 
  apply_context_notation + 
  Hole_notation +
  compose_context_notation +
  subst_context_notation

end
