theory RealTimeDeque_Aux
  imports RealTimeDeque States_Aux
begin

text\<open>
 \<^descr> \<open>listL\<close>, \<open>listR\<close>: Get all elements of the deque in a list starting at the left or right end. 
   They are needed as list abstractions for the correctness proofs.
\<close>

fun listL :: "'a deque \<Rightarrow> 'a list" where
  "listL Empty = []"
| "listL (One x) = [x]"
| "listL (Two x y) = [x, y]"
| "listL (Three x y z) = [x, y, z]"
| "listL (Idles left right) = Idle_Aux.list left @ (rev (Idle_Aux.list right))"
| "listL (Rebal states) = States_Aux.listL states"

abbreviation listR :: "'a deque \<Rightarrow> 'a list" where
  "listR deque \<equiv> rev (listL deque)"

instantiation deque::(type) invar
begin

fun invar_deque :: "'a deque \<Rightarrow> bool" where
  "invar Empty = True"
| "invar (One _) = True"
| "invar (Two _ _) = True"
| "invar (Three _ _ _) = True"
| "invar (Idles left right) \<longleftrightarrow>
   invar left  \<and>
   invar right \<and>
   \<not> is_empty left  \<and> 
   \<not> is_empty right \<and>
   3 * size right \<ge> size left \<and>
   3 * size left \<ge> size right
  "
| "invar (Rebal states) \<longleftrightarrow> 
   invar states \<and>
   size_ok states \<and>
   0 < remaining_steps states
  "

instance..
end

end
