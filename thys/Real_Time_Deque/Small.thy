section \<open>Smaller End of Deque\<close>

theory Small
imports Common
begin

text \<open>
\<^noindent> The smaller end of the deque during \<open>transformation\<close> can be in one three phases:

 \<^descr> \<open>Reverse1\<close>: Using the \<open>step\<close> function the originally contained elements are reversed.
 \<^descr> \<open>Reverse2\<close>: Using the \<open>step\<close> function the newly obtained elements from the bigger end are reversed on top of the ones reversed in the previous phase.
 \<^descr> \<open>Common\<close>: See theory \<open>Common\<close>. Is used to reverse the elements from the two previous phases again to get them again in the original order.

\<^noindent> Each phase contains a \<open>current\<close> state, which holds the original elements of the deque end. 
\<close>

datatype (plugins del: size) 'a small_state =
   Reverse1 "'a current" "'a stack" "'a list"
 | Reverse2 "'a current" "'a list" "'a stack" "'a list" nat
 | Common "'a common_state"

text \<open>\<^noindent> Functions:

 \<^descr> \<open>push\<close>, \<open>pop\<close>: Add and remove elements using the \<open>current\<close> state.
 \<^descr> \<open>step\<close>: Executes one step of the transformation, while keeping the invariant.\<close>

instantiation small_state::(type) step
begin

fun step_small_state :: "'a small_state \<Rightarrow> 'a small_state" where
  "step (Common state) = Common (step state)"
| "step (Reverse1 current small auxS) = (
    if is_empty small 
    then Reverse1 current small auxS 
    else Reverse1 current (Stack.pop small) ((Stack.first small)#auxS)
  )"
| "step (Reverse2 current auxS big newS count) = (
    if is_empty big
    then Common (normalize (Copy current auxS newS count))
    else Reverse2 current auxS (Stack.pop big) ((Stack.first big)#newS) (count + 1)
  )"

instance..
end

fun push :: "'a \<Rightarrow> 'a small_state \<Rightarrow> 'a small_state" where
  "push x (Common state) = Common (Common.push x state)"
| "push x (Reverse1 current small auxS) = Reverse1 (Current.push x current) small auxS"
| "push x (Reverse2 current auxS big newS count) = 
    Reverse2 (Current.push x current) auxS big newS count"

fun pop :: "'a small_state \<Rightarrow> 'a * 'a small_state" where
  "pop (Common state) = (
    let (x, state) = Common.pop state 
    in (x, Common state)
  )"
| "pop (Reverse1 current small auxS) = 
    (first current, Reverse1 (drop_first current) small auxS)"
| "pop (Reverse2 current auxS big newS count) = 
    (first current, Reverse2 (drop_first current) auxS big newS count)"

end