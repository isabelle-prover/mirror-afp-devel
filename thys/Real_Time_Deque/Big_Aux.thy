theory Big_Aux
imports Big Common_Aux
begin    

text \<open>\<^noindent> Functions:

\<^descr> \<open>size_new\<close>: Returns the size that the deque end will have after the transformation is finished.
\<^descr> \<open>size\<close>: Minimum of \<open>size_new\<close> and the number of elements contained in the current state.
\<^descr> \<open>remaining_steps\<close>: Returns how many steps are left until the transformation is finished.
\<^descr> \<open>list\<close>: List abstraction of the elements which this end will contain after the transformation is finished
\<^descr> \<open>list_current\<close>: List abstraction of the elements currently in this deque end.\<close>

fun list :: "'a state \<Rightarrow> 'a list" where
  "list (Common common) = Common_Aux.list common"
| "list (Reverse (Current extra _ _ remained) big aux count) = (
   let reversed = reverseN count (Stack_Aux.list big) aux in
    extra @ (reverseN remained reversed [])
  )"

fun list_current :: "'a state \<Rightarrow> 'a list" where
  "list_current (Common common) = Common_Aux.list_current common"
| "list_current (Reverse current _ _ _) = Current_Aux.list current"

instantiation state ::(type) invar
begin

fun invar_state :: "'a state \<Rightarrow> bool" where
  "invar (Common state) \<longleftrightarrow> invar state"
| "invar (Reverse current big aux count) \<longleftrightarrow> (
   case current of Current extra added old remained \<Rightarrow>
      invar current
    \<and> List.length aux \<ge> remained - count
    
    \<and> count \<le> size big
    \<and> Stack_Aux.list old = rev (take (size old) ((rev (Stack_Aux.list big)) @ aux))
    \<and> take remained (Stack_Aux.list old) = 
      rev (take remained (reverseN count (Stack_Aux.list big) aux))
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
