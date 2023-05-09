section \<open>Bigger End of Deque\<close>

theory Big
imports Common
begin

text \<open>\<^noindent> The bigger end of the deque during rebalancing can be in two phases:

 \<^descr> \<open>Big1\<close>: Using the \<open>step\<close> function the originally contained elements, 
    which will be kept in this end, are reversed.
 \<^descr> \<open>Big2\<close>: Specified in theory \<open>Common\<close>. Is used to reverse the elements from the previous phase 
    again to get them in the original order.

\<^noindent> Each phase contains a \<open>current\<close> state, which holds the original elements of the deque end. 
\<close>

datatype (plugins del: size) 'a big_state = 
     Big1 "'a current" "'a stack" "'a list" nat
   | Big2 "'a common_state"

text \<open>\<^noindent> Functions:

\<^descr> \<open>push\<close>, \<open>pop\<close>: Add and remove elements using the \<open>current\<close> state.
\<^descr> \<open>step\<close>: Executes one step of the rebalancing\<close>

instantiation big_state ::(type) step
begin

fun step_big_state :: "'a big_state \<Rightarrow> 'a big_state" where
  "step (Big2 state) = Big2 (step state)"
| "step (Big1 current _ aux 0) = Big2 (normalize (Copy current aux [] 0))"
| "step (Big1 current big aux count) = 
     Big1 current (Stack.pop big) ((Stack.first big)#aux) (count - 1)"

instance..
end

fun push :: "'a \<Rightarrow> 'a big_state \<Rightarrow> 'a big_state" where
  "push x (Big2 state) = Big2 (Common.push x state)"
| "push x (Big1 current big aux count) = Big1 (Current.push x current) big aux count"

fun pop :: "'a big_state \<Rightarrow> 'a * 'a big_state" where
  "pop (Big2 state) = (let (x, state) = Common.pop state in (x, Big2 state))"
| "pop (Big1 current big aux count) = 
    (first current, Big1 (drop_first current) big aux count)"

end
