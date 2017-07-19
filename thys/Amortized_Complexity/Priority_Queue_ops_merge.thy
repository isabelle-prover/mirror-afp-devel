theory Priority_Queue_ops_merge
imports Main
begin

datatype 'a op\<^sub>p\<^sub>q = Empty | Insert 'a | Del_min | Merge

fun arity :: "'a op\<^sub>p\<^sub>q \<Rightarrow> nat" where
"arity Empty = 0" |
"arity (Insert _) = 1" |
"arity Del_min = 1" |
"arity Merge = 2"

end
