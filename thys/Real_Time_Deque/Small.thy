section \<open>Smaller End of Deque\<close>

theory Small
imports Common
begin

text \<open>
\<^noindent> The smaller end of the deque during \<open>Rebalancing\<close> can be in one three phases:

 \<^descr> \<open>Small1\<close>: Using the \<open>step\<close> function the originally contained elements are reversed.
 \<^descr> \<open>Small2\<close>: Using the \<open>step\<close> function the newly obtained elements from the bigger end are reversed on top of the ones reversed in the previous phase.
 \<^descr> \<open>Small3\<close>: See theory \<open>Common\<close>. Is used to reverse the elements from the two previous phases again to get them again in the original order.

\<^noindent> Each phase contains a \<open>current\<close> state, which holds the original elements of the deque end. 
\<close>

datatype (plugins del: size) 'a small_state =
   Small1 "'a current" "'a stack" "'a list"
 | Small2 "'a current" "'a list" "'a stack" "'a list" nat
 | Small3 "'a common_state"

text \<open>\<^noindent> Functions:

 \<^descr> \<open>push\<close>, \<open>pop\<close>: Add and remove elements using the \<open>current\<close> state.
 \<^descr> \<open>step\<close>: Executes one step of the rebalancing, while keeping the invariant.\<close>

instantiation small_state::(type) step
begin

fun step_small_state :: "'a small_state \<Rightarrow> 'a small_state" where
  "step (Small3 state) = Small3 (step state)"
| "step (Small1 current small auxS) = (
    if is_empty small 
    then Small1 current small auxS 
    else Small1 current (Stack.pop small) ((Stack.first small)#auxS)
  )"
| "step (Small2 current auxS big newS count) = (
    if is_empty big
    then Small3 (normalize (Copy current auxS newS count))
    else Small2 current auxS (Stack.pop big) ((Stack.first big)#newS) (count + 1)
  )"

instance..
end

fun push :: "'a \<Rightarrow> 'a small_state \<Rightarrow> 'a small_state" where
  "push x (Small3 state) = Small3 (Common.push x state)"
| "push x (Small1 current small auxS) = Small1 (Current.push x current) small auxS"
| "push x (Small2 current auxS big newS count) = 
    Small2 (Current.push x current) auxS big newS count"

fun pop :: "'a small_state \<Rightarrow> 'a * 'a small_state" where
  "pop (Small3 state) = (
    let (x, state) = Common.pop state 
    in (x, Small3 state)
  )"
| "pop (Small1 current small auxS) = 
    (first current, Small1 (drop_first current) small auxS)"
| "pop (Small2 current auxS big newS count) = 
    (first current, Small2 (drop_first current) auxS big newS count)"

end