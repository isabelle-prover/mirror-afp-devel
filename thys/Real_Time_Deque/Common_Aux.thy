theory Common_Aux
imports Common Current_Aux Idle_Aux
begin

text\<open>
\<^noindent> Functions:

\<^descr> \<open>list\<close>: List abstraction of the elements which this end will contain after the rebalancing is finished
\<^descr> \<open>list_current\<close>: List abstraction of the elements currently in this deque end.
\<^descr> \<open>remaining_steps\<close>: Returns how many steps are left until the rebalancing is finished.
\<^descr> \<open>size_new\<close>: Returns the size, that the deque end will have after the rebalancing is finished.
\<^descr> \<open>size\<close>: Minimum of \<open>size_new\<close> and the number of elements contained in the \<open>current\<close> state.\<close>

definition take_rev where 
[simp]:  "take_rev n xs = rev (take n xs)"

fun list :: "'a common_state \<Rightarrow> 'a list" where
  "list (Idle _ idle) = Idle_Aux.list idle"
| "list (Copy (Current extra _ _ remained) old new moved) 
   = extra @ take_rev (remained - moved) old @ new"

fun list_current :: "'a common_state \<Rightarrow> 'a list" where
  "list_current (Idle current _) = Current_Aux.list current"
| "list_current (Copy current _ _ _) = Current_Aux.list current"

instantiation common_state::(type) invar
begin

fun invar_common_state :: "'a common_state \<Rightarrow> bool" where
  "invar (Idle current idle) \<longleftrightarrow>
      invar idle 
    \<and> invar current 
    \<and> size_new current = size idle
    \<and> take (size idle) (Current_Aux.list current) = 
      take (size current) (Idle_Aux.list idle)"
| "invar (Copy current aux new moved) \<longleftrightarrow> (
    case current of Current _ _ old remained \<Rightarrow>
      moved < remained
    \<and> moved = length new
    \<and> remained \<le> length aux + moved
    \<and> invar current
    \<and> take remained (Stack_Aux.list old) = take (size old) (take_rev (remained - moved) aux @ new)
 )"

instance..
end

instantiation common_state::(type) size
begin

fun size_common_state :: "'a common_state \<Rightarrow> nat" where
  "size (Idle current idle) = min (size current) (size idle)"
| "size (Copy current _ _ _) = min (size current) (size_new current)"

instance..
end

instantiation common_state::(type) size_new
begin

fun size_new_common_state :: "'a common_state \<Rightarrow> nat" where
  "size_new (Idle current _) = size_new current"
| "size_new (Copy current _ _ _) = size_new current"

instance..
end

instantiation common_state::(type) remaining_steps
begin

fun remaining_steps_common_state :: "'a common_state \<Rightarrow> nat" where
  "remaining_steps (Idle _ _) = 0"
| "remaining_steps (Copy (Current _ _ _ remained) aux new moved) = remained - moved"

instance..
end


end
