theory Stack_Aux
imports Stack
begin

fun list :: "'a stack \<Rightarrow> 'a list" where
  "list (Stack left right) = left @ right"

instantiation stack ::(type) size
begin

fun size_stack :: "'a stack \<Rightarrow> nat" where
  "size (Stack left right) = length left + length right"

instance..
end

end
