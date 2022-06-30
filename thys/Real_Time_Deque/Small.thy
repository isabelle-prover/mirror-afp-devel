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

datatype (plugins del: size) 'a state =
   Reverse1 "'a current" "'a stack" "'a list"
 | Reverse2 "'a current" "'a list" "'a stack" "'a list" nat
 | Common "'a Common.state"

text \<open>\<^noindent> Functions:

 \<^descr> \<open>push\<close>, \<open>pop\<close>: Add and remove elements using the \<open>current\<close> state.
 \<^descr> \<open>step\<close>: Executes one step of the transformation, while keeping the invariant.
 \<^descr> \<open>size_new\<close>: Returns the size, that the deque end will have after the transformation is finished.
 \<^descr> \<open>size\<close>: Minimum of \<open>size_new\<close> and the number of elements contained in the `current` state.
 \<^descr> \<open>list\<close>: List abstraction of the elements which this end will contain after the transformation is finished. The first phase is not covered, since the elements, which will be transferred from the bigger deque end are not known yet.
 \<^descr> \<open>list_current\<close>: List abstraction of the elements currently in this deque end.
\<close>

fun list :: "'a state \<Rightarrow> 'a list" where
  "list (Common common) = Common.list common"
| "list (Reverse2 (Current extra _ _ remained) aux big new count) =
  extra @ reverseN (remained - (count + size big)) aux (rev (Stack.list big) @ new)"

fun list_current :: "'a state \<Rightarrow> 'a list" where
  "list_current (Common common) = Common.list_current common"
| "list_current (Reverse2 current _ _ _ _) = Current.list current"
| "list_current (Reverse1 current _ _) = Current.list current"

instantiation state::(type) step
begin

fun step_state :: "'a state \<Rightarrow> 'a state" where
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

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Common state) = Common (Common.push x state)"
| "push x (Reverse1 current small auxS) = Reverse1 (Current.push x current) small auxS"
| "push x (Reverse2 current auxS big newS count) = 
    Reverse2 (Current.push x current) auxS big newS count"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Common state) = (
    let (x, state) = Common.pop state 
    in (x, Common state)
  )"
| "pop (Reverse1 current small auxS) = 
    (first current, Reverse1 (drop_first current) small auxS)"
| "pop (Reverse2 current auxS big newS count) = 
    (first current, Reverse2 (drop_first current) auxS big newS count)"

instantiation state::(type) is_empty
begin

fun is_empty_state :: "'a state \<Rightarrow> bool" where
  "is_empty (Common state) = is_empty state"
| "is_empty (Reverse1 current _ _) = is_empty current"
| "is_empty (Reverse2 current _ _ _ _) = is_empty current"

instance..
end

instantiation state::(type) invar
begin

fun invar_state :: "'a state \<Rightarrow> bool" where
  "invar (Common state) = invar state"
| "invar (Reverse2 current auxS big newS count) = (
   case current of Current _ _ old remained \<Rightarrow>
      remained = count + size big + size old
    \<and> remained \<ge> size old
    \<and> count = List.length newS
    \<and> invar current
    \<and> List.length auxS \<ge> size old
    \<and> Stack.list old = rev (take (size old) auxS)
  )"
| "invar (Reverse1 current small auxS) = (
   case current of Current _ _ old remained \<Rightarrow>
      invar current
    \<and> remained \<ge> size old
    \<and> size small + List.length auxS \<ge> size old
    \<and> Stack.list old = rev (take (size old) (rev (Stack.list small) @ auxS))
  )"

instance..
end

instantiation state::(type) size
begin

fun size_state :: "'a state \<Rightarrow> nat" where
  "size (Common state) = size state"
| "size (Reverse2 current _ _ _ _) = min (size current) (size_new current)"
| "size (Reverse1 current _ _) = min (size current) (size_new current)"

instance..
end

instantiation state::(type) size_new
begin

fun size_new_state :: "'a state \<Rightarrow> nat" where
  "size_new (Common state) = size_new state"
| "size_new (Reverse2 current _ _ _ _) = size_new current"
| "size_new (Reverse1 current _ _) = size_new current"

instance..
end

end