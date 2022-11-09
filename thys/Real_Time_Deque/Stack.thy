section \<open>Stack\<close>

theory Stack
imports Type_Classes
begin

text \<open>A datatype encapsulating two lists. Is used as a base data-structure in different places.
It has the operations \<open>push\<close>, \<open>pop\<close> and \<open>first\<close>.\<close>

datatype (plugins del: size) 'a stack = Stack "'a list" "'a list"

fun push :: "'a \<Rightarrow> 'a stack \<Rightarrow> 'a stack" where
  "push x (Stack left right) = Stack (x#left) right"

fun pop :: "'a stack \<Rightarrow> 'a stack" where
  "pop (Stack [] [])              = Stack [] []"
| "pop (Stack (x#left) right)     = Stack left right"
| "pop (Stack []       (x#right)) = Stack []   right"

fun first :: "'a stack \<Rightarrow> 'a" where
  "first (Stack (x#left) right)     = x"
| "first (Stack []       (x#right)) = x"

instantiation stack ::(type) is_empty
begin

fun is_empty_stack where
  "is_empty_stack (Stack [] []) = True" 
| "is_empty_stack _             = False"

instance..
end

end