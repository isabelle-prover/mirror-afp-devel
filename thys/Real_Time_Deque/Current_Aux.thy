theory Current_Aux
imports Current Stack_Aux
begin

text \<open>Specification functions:
\<^descr> \<open>list\<close>: list abstraction for the originally contained elements of a deque end during transformation.
\<^descr> \<open>invar\<close>: Is the stored number of newly added elements correct?
\<^descr> \<open>size\<close>: The number of the originally contained elements.
\<^descr> \<open>size_new\<close>: Number of elements which will be contained after the transformation is finished.\<close>

fun list :: "'a current \<Rightarrow> 'a list" where
  "list (Current extra _ old _) = extra @ (Stack_Aux.list old)"

instantiation current::(type) invar
begin

fun invar_current :: "'a current \<Rightarrow> bool" where
  "invar (Current extra added _ _) \<longleftrightarrow> length extra = added"

instance..
end

instantiation current::(type) size
begin

fun size_current :: "'a current \<Rightarrow> nat" where
  "size (Current _ added old _) = added + size old"

instance..
end

instantiation current::(type) size_new
begin

fun size_new_current :: "'a current \<Rightarrow> nat" where
  "size_new (Current _ added _ remained) = added + remained"

instance..
end

end
