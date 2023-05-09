section \<open>Current Stack\<close>

theory Current
imports Stack
begin

text \<open>
\noindent This data structure is composed of:
\<^item> the newly added elements to one end of a deque during the rebalancing phase
\<^item> the number of these newly added elements 
\<^item> the originally contained elements
\<^item> the number of elements which will be contained after the rebalancing is finished.
\<close>

datatype (plugins del: size) 'a current = Current "'a list" nat "'a stack" nat

fun push :: "'a \<Rightarrow> 'a current \<Rightarrow> 'a current" where
  "push x (Current extra added old remained) = Current (x#extra) (added + 1) old remained"

fun pop :: "'a current \<Rightarrow> 'a * 'a current" where
  "pop (Current [] added old remained)     = 
    (first old, Current [] added (Stack.pop old) (remained - 1))"
| "pop (Current (x#xs) added old remained) = 
    (x, Current xs (added - 1) old remained)"

fun first :: "'a current \<Rightarrow> 'a" where
  "first current = fst (pop current)"

abbreviation drop_first :: "'a current \<Rightarrow> 'a current" where
  "drop_first current \<equiv> snd (pop current)"

end
