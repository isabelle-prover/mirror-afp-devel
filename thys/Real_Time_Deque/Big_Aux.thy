theory Big_Aux
imports Big Common_Aux
begin    

text \<open>\<^noindent> Functions:

\<^descr> \<open>size_new\<close>: Returns the size that the deque end will have after the rebalancing is finished.
\<^descr> \<open>size\<close>: Minimum of \<open>size_new\<close> and the number of elements contained in the current state.
\<^descr> \<open>remaining_steps\<close>: Returns how many steps are left until the rebalancing is finished.
\<^descr> \<open>list\<close>: List abstraction of the elements which this end will contain after the rebalancing is finished
\<^descr> \<open>list_current\<close>: List abstraction of the elements currently in this deque end.\<close>

fun list :: "'a big_state \<Rightarrow> 'a list" where
  "list (Big2 common) = Common_Aux.list common"
| "list (Big1 (Current extra _ _ remained) big aux count) = (
   let reversed = take_rev count (Stack_Aux.list big) @ aux in
    extra @ (take_rev remained reversed)
  )"

fun list_current :: "'a big_state \<Rightarrow> 'a list" where
  "list_current (Big2 common) = Common_Aux.list_current common"
| "list_current (Big1 current _ _ _) = Current_Aux.list current"

instantiation big_state ::(type) invar
begin

fun invar_big_state :: "'a big_state \<Rightarrow> bool" where
  "invar (Big2 state) \<longleftrightarrow> invar state"
| "invar (Big1 current big aux count) \<longleftrightarrow> (
   case current of Current extra added old remained \<Rightarrow>
      invar current
    \<and> remained \<le> length aux + count
    \<and> count \<le> size big
    \<and> Stack_Aux.list old = rev (take (size old) ((rev (Stack_Aux.list big)) @ aux))
    \<and> take remained (Stack_Aux.list old) = 
      rev (take remained (take_rev count (Stack_Aux.list big) @ aux))
)"

instance..
end

instantiation big_state ::(type) size
begin

fun size_big_state :: "'a big_state \<Rightarrow> nat" where
  "size (Big2 state) = size state"
| "size (Big1 current _ _ _) = min (size current) (size_new current)"

instance..
end

instantiation big_state ::(type) size_new
begin

fun size_new_big_state :: "'a big_state \<Rightarrow> nat" where
  "size_new (Big2 state) = size_new state"
| "size_new (Big1 current _ _ _) = size_new current"

instance..
end

instantiation big_state ::(type) remaining_steps
begin

fun remaining_steps_big_state :: "'a big_state \<Rightarrow> nat" where
  "remaining_steps (Big2 state) = remaining_steps state"
| "remaining_steps (Big1 (Current _ _ _ remaining) _ _ count) = count + remaining + 1"

instance..
end

end
