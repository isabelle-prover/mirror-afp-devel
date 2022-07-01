section \<open>Current Stack\<close>

theory Current
imports Stack
begin

text \<open>
\noindent This data structure is composed of:
\<^item> the newly added elements to one end of a deque during the transformation phase
\<^item> the number of these newly added elements 
\<^item> the originally contained elements
\<^item> the number of elements which will be contained after the transformation is finished.
\<close>

datatype (plugins del: size) 'a current = Current "'a list" nat "'a stack" nat

text \<open>Specification functions:
\<^descr> \<open>list\<close>: list abstraction for the originally contained elements of a deque end during transformation.
\<^descr> \<open>invar\<close>: Is the stored number of newly added elements correct?
\<^descr> \<open>size\<close>: The number of the originally contained elements.
\<^descr> \<open>size_new\<close>: Number of elements which will be contained after the transformation is finished.
\<close>

fun push :: "'a \<Rightarrow> 'a current \<Rightarrow> 'a current" where
  "push x (Current extra added old remained) = Current (x#extra) (added + 1) old remained"

fun pop :: "'a current \<Rightarrow> 'a * 'a current" where
  "pop (Current [] added old remained)     = (first old, Current [] added (Stack.pop old) (remained - 1))"
| "pop (Current (x#xs) added old remained) = (x, Current xs (added - 1) old remained)"

fun first :: "'a current \<Rightarrow> 'a" where
  "first current = fst (pop current)"

abbreviation drop_first :: "'a current \<Rightarrow> 'a current" where
  "drop_first current \<equiv> snd (pop current)"

fun list :: "'a current \<Rightarrow> 'a list" where
  "list (Current extra _ old _) = extra @ (Stack.list old)"

instantiation current::(type) is_empty
begin

(* TODO: Actually it should be "added + remained = 0" Maybe directly base it on size? *) 
fun is_empty_current :: "'a current \<Rightarrow> bool" where
  "is_empty (Current extra _ old remained) \<longleftrightarrow> is_empty old \<and> extra = [] \<or> remained = 0"

instance..
end

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
