section \<open>Idle\<close>

theory Idle
imports Stack
begin

text \<open>Represents the `idle' state of one deque end.
It contains a \<open>stack\<close> and its size as a natural number.\<close>

datatype (plugins del: size) 'a idle = Idle "'a stack" nat

fun push :: "'a \<Rightarrow> 'a idle \<Rightarrow> 'a idle" where
  "push x (Idle stack stackSize) = Idle (Stack.push x stack) (Suc stackSize)"

fun pop :: "'a idle \<Rightarrow> ('a * 'a idle)" where
  "pop (Idle stack stackSize) = (Stack.first stack, Idle (Stack.pop stack) (stackSize - 1))"
  
end
