theory Stack_Aux
imports Stack
begin

text\<open>The function \<open>list\<close> appends the two lists and is needed for the list abstraction of the deque.\<close>

fun list :: "'a stack \<Rightarrow> 'a list" where
  "list (Stack left right) = left @ right"

instantiation stack ::(type) size
begin

fun size_stack :: "'a stack \<Rightarrow> nat" where
  "size (Stack left right) = length left + length right"

instance..
end

end
