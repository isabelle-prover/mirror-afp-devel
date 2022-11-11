theory Small_Aux
imports Small Common_Aux
begin

text \<open>\<^noindent> Functions:
 \<^descr> \<open>size_new\<close>: Returns the size, that the deque end will have after the transformation is finished.
 \<^descr> \<open>size\<close>: Minimum of \<open>size_new\<close> and the number of elements contained in the `current` state.
 \<^descr> \<open>list\<close>: List abstraction of the elements which this end will contain after the transformation is finished. The first phase is not covered, since the elements, which will be transferred from the bigger deque end are not known yet.
 \<^descr> \<open>list_current\<close>: List abstraction of the elements currently in this deque end.\<close>

fun list :: "'a state \<Rightarrow> 'a list" where
  "list (Common common) = Common_Aux.list common"
| "list (Reverse2 (Current extra _ _ remained) aux big new count) =
  extra @ (take_rev (remained - (count + size big)) aux) @ (rev (Stack_Aux.list big) @ new)"

fun list_current :: "'a state \<Rightarrow> 'a list" where
  "list_current (Common common) = Common_Aux.list_current common"
| "list_current (Reverse2 current _ _ _ _) = Current_Aux.list current"
| "list_current (Reverse1 current _ _) = Current_Aux.list current"

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
    \<and> Stack_Aux.list old = rev (take (size old) auxS)
  )"
| "invar (Reverse1 current small auxS) = (
   case current of Current _ _ old remained \<Rightarrow>
      invar current
    \<and> remained \<ge> size old
    \<and> size small + List.length auxS \<ge> size old
    \<and> Stack_Aux.list old = rev (take (size old) (rev (Stack_Aux.list small) @ auxS))
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