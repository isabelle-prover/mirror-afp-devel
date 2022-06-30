section \<open>Bigger End of Deque\<close>

theory Big
imports Common
begin

text \<open>\<^noindent> The bigger end of the deque during transformation can be in two phases:

 \<^descr> \<open>Reverse\<close>: Using the \<open>step\<close> function the originally contained elements, which will be kept in this end, are reversed.
 \<^descr> \<open>Common\<close>: Specified in theory \<open>Common\<close>. Is used to reverse the elements from the previous phase again to get them in the original order.

\<^noindent> Each phase contains a \<open>current\<close> state, which holds the original elements of the deque end. 
\<close>

datatype (plugins del: size) 'a state = 
     Reverse "'a current" "'a stack" "'a list" nat
   | Common "'a Common.state"

text \<open>\<^noindent> Functions:

\<^descr> \<open>step\<close>: Executes one step of the transformation
\<^descr> \<open>size_new\<close>: Returns the size that the deque end will have after the transformation is finished.
\<^descr> \<open>size\<close>: Minimum of \<open>size_new\<close> and the number of elements contained in the current state.
\<^descr> \<open>remaining_steps\<close>: Returns how many steps are left until the transformation is finished.
\<^descr> \<open>list\<close>: List abstraction of the elements which this end will contain after the transformation is finished
\<^descr> \<open>list_current\<close>: List abstraction of the elements currently in this deque end.
\<close>

fun list :: "'a state \<Rightarrow> 'a list" where
  "list (Common common) = Common.list common"
| "list (Reverse (Current extra _ _ remained) big aux count) = (
   let reversed = reverseN count (Stack.list big) aux in
    extra @ (reverseN remained reversed [])
  )"

fun list_current :: "'a state \<Rightarrow> 'a list" where
  "list_current (Common common) = Common.list_current common"
| "list_current (Reverse current _ _ _) = Current.list current"

instantiation state ::(type) step
begin

fun step_state :: "'a state \<Rightarrow> 'a state" where
  "step (Common state) = Common (step state)"
| "step (Reverse current _ aux 0) = Common (normalize (Copy current aux [] 0))"
| "step (Reverse current big aux count) = 
     Reverse current (Stack.pop big) ((Stack.first big)#aux) (count - 1)"

instance..
end

fun push :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state" where
  "push x (Common state) = Common (Common.push x state)"
| "push x (Reverse current big aux count) = Reverse (Current.push x current) big aux count"

fun pop :: "'a state \<Rightarrow> 'a * 'a state" where
  "pop (Common state) = (let (x, state) = Common.pop state in (x, Common state))"
| "pop (Reverse current big aux count) = (first current, Reverse (drop_first current) big aux count)"

instantiation state ::(type) is_empty
begin

fun is_empty_state :: "'a state \<Rightarrow> bool" where
  "is_empty (Common state) = is_empty state"
| "is_empty (Reverse current _ _ count) = (
    case current of Current extra added old remained \<Rightarrow> 
      is_empty current \<or> remained \<le> count
)"

instance..
end

instantiation state ::(type) invar
begin

fun invar_state :: "'a state \<Rightarrow> bool" where
  "invar (Common state) \<longleftrightarrow> invar state"
| "invar (Reverse current big aux count) \<longleftrightarrow> (
   case current of Current extra added old remained \<Rightarrow>
      invar current
    \<and> List.length aux \<ge> remained - count
    
    \<and> count \<le> size big
    \<and> Stack.list old = rev (take (size old) ((rev (Stack.list big)) @ aux))
    \<and> take remained (Stack.list old) = rev (take remained (reverseN count (Stack.list big) aux))
)"

instance..
end

instantiation state ::(type) size
begin

fun size_state :: "'a state \<Rightarrow> nat" where
  "size (Common state) = size state"
| "size (Reverse current _ _ _) = min (size current) (size_new current)"

instance..
end

instantiation state ::(type) size_new
begin

fun size_new_state :: "'a state \<Rightarrow> nat" where
  "size_new (Common state) = size_new state"
| "size_new (Reverse current _ _ _) = size_new current"

instance..
end

instantiation state ::(type) remaining_steps
begin

fun remaining_steps_state :: "'a state \<Rightarrow> nat" where
  "remaining_steps (Common state) = remaining_steps state"
| "remaining_steps (Reverse (Current _ _ _ remaining) _ _ count) = count + remaining + 1"

instance..
end

end