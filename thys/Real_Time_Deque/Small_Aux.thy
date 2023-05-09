theory Small_Aux
imports Small Common_Aux
begin

text \<open>\<^noindent> Functions:
 \<^descr> \<open>size_new\<close>: Returns the size, that the deque end will have after the rebalancing is finished.
 \<^descr> \<open>size\<close>: Minimum of \<open>size_new\<close> and the number of elements contained in the `current` state.
 \<^descr> \<open>list\<close>: List abstraction of the elements which this end will contain after the rebalancing is finished. The first phase is not covered, since the elements, which will be transferred from the bigger deque end are not known yet.
 \<^descr> \<open>list_current\<close>: List abstraction of the elements currently in this deque end.\<close>

fun list :: "'a small_state \<Rightarrow> 'a list" where
  "list (Small3 common) = Common_Aux.list common"
| "list (Small2 (Current extra _ _ remained) aux big new count) =
  extra @ (take_rev (remained - (count + size big)) aux) @ (rev (Stack_Aux.list big) @ new)"

fun list_current :: "'a small_state \<Rightarrow> 'a list" where
  "list_current (Small3 common) = Common_Aux.list_current common"
| "list_current (Small2 current _ _ _ _) = Current_Aux.list current"
| "list_current (Small1 current _ _) = Current_Aux.list current"

instantiation small_state::(type) invar
begin

fun invar_small_state :: "'a small_state \<Rightarrow> bool" where
  "invar (Small3 state) = invar state"
| "invar (Small2 current auxS big newS count) = (
   case current of Current _ _ old remained \<Rightarrow>
      remained = count + size big + size old
    \<and> count = List.length newS
    \<and> invar current
    \<and> List.length auxS \<ge> size old
    \<and> Stack_Aux.list old = rev (take (size old) auxS)
  )"
| "invar (Small1 current small auxS) = (
   case current of Current _ _ old remained \<Rightarrow>
      invar current
    \<and> remained \<ge> size old
    \<and> size small + List.length auxS \<ge> size old
    \<and> Stack_Aux.list old = rev (take (size old) (rev (Stack_Aux.list small) @ auxS))
  )"

instance..
end

instantiation small_state::(type) size
begin

fun size_small_state :: "'a small_state \<Rightarrow> nat" where
  "size (Small3 state) = size state"
| "size (Small2 current _ _ _ _) = min (size current) (size_new current)"
| "size (Small1 current _ _) = min (size current) (size_new current)"

instance..
end

instantiation small_state::(type) size_new
begin

fun size_new_small_state :: "'a small_state \<Rightarrow> nat" where
  "size_new (Small3 state) = size_new state"
| "size_new (Small2 current _ _ _ _) = size_new current"
| "size_new (Small1 current _ _) = size_new current"

instance..
end

end
