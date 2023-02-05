theory Reduction

imports 
  Main
begin 

section \<open>Reduction Function\<close>
text \<open>This definition was taken from the developements at 
  \url{https://github.com/wimmers/poly-reductions}
  ``Karp21/Reductions.thy''.
  TODO: When this repo comes into the AFP, link to original definition.\<close>
definition is_reduction :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "is_reduction f A B \<equiv> \<forall>a. a \<in> A \<longleftrightarrow> f a \<in> B "
end