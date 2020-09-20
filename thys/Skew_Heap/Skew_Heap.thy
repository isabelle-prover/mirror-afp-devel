section "Skew Heap"

theory Skew_Heap
imports
  "HOL-Library.Tree_Multiset"
  "HOL-Library.Pattern_Aliases"
  "HOL-Data_Structures.Priority_Queue_Specs"
begin

unbundle pattern_aliases

text\<open>Skew heaps~\cite{SleatorT-SIAM86} are possibly the simplest functional
priority queues that have logarithmic (albeit amortized) complexity.

The implementation below should be generalized to separate the elements from
their priorities.\<close>


subsection "Get Minimum"

fun get_min :: "('a::linorder) tree \<Rightarrow> 'a" where
"get_min(Node l m r) = m"

lemma get_min: "\<lbrakk> heap t;  t \<noteq> Leaf \<rbrakk> \<Longrightarrow> get_min t = Min_mset (mset_tree t)"
by (auto simp add: eq_Min_iff neq_Leaf_iff)

subsection "Merge"

function merge :: "('a::linorder) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"merge Leaf t = t" |
"merge t Leaf = t" |
"merge (Node l1 a1 r1 =: t1) (Node l2 a2 r2 =: t2) =
   (if a1 \<le> a2 then Node (merge t2 r1) a1 l1
    else Node (merge t1 r2) a2 l2)" 
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

lemma merge_code: "merge t1 t2 =
  (case t1 of
   Leaf \<Rightarrow> t2 |
   Node l1 a1 r1 \<Rightarrow> (case t2 of
     Leaf \<Rightarrow> t1 |
     Node l2 a2 r2 \<Rightarrow> 
       (if a1 \<le> a2
        then Node (merge t2 r1) a1 l1
        else Node (merge t1 r2) a2 l2)))"
by(auto split: tree.split)

text\<open>An alternative version that always walks to the Leaf of both heaps:\<close>
function merge2 :: "('a::linorder) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"merge2 Leaf Leaf = Leaf" |
"merge2 Leaf (Node l2 a2 r2) = Node (merge2 r2 Leaf) a2 l2" |
"merge2 (Node l1 a1 r1) Leaf = Node (merge2 r1 Leaf) a1 l1" |
"merge2 (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2
    then Node (merge2 (Node l2 a2 r2) r1) a1 l1
    else Node (merge2 (Node l1 a1 r1) r2) a2 l2)"
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

lemma size_merge[simp]: "size(merge t1 t2) = size t1 + size t2"
by(induction t1 t2 rule: merge.induct) auto

lemma size_merge2[simp]: "size(merge2 t1 t2) = size t1 + size t2"
by(induction t1 t2 rule: merge2.induct) auto

lemma mset_merge: "mset_tree (merge t1 t2) = mset_tree t1 + mset_tree t2"
by (induction t1 t2 rule: merge.induct) (auto simp add: ac_simps)

lemma set_merge: "set_tree (merge t1 t2) = set_tree t1 \<union> set_tree t2"
by (metis mset_merge set_mset_tree set_mset_union)

lemma heap_merge:
  "heap t1 \<Longrightarrow> heap t2 \<Longrightarrow> heap (merge t1 t2)"
by (induction t1 t2 rule: merge.induct)(auto simp: ball_Un set_merge)


subsection "Insert"

hide_const (open) insert

definition insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert a t = merge (Node Leaf a Leaf) t"

lemma heap_insert: "heap t \<Longrightarrow> heap (insert a t)"
by (simp add: insert_def heap_merge)

lemma mset_insert: "mset_tree (insert a t) = {#a#} + mset_tree t"
by (auto simp: mset_merge insert_def)


subsection "Delete minimum"

fun del_min :: "'a::linorder tree \<Rightarrow> 'a tree" where
"del_min Leaf = Leaf" |
"del_min (Node l m r) = merge l r"

lemma heap_del_min: "heap t \<Longrightarrow> heap (del_min t)"
by (cases t) (auto simp: heap_merge)

lemma mset_del_min: "mset_tree (del_min t) = mset_tree t - {# get_min t #}"
by (cases t) (auto simp: mset_merge ac_simps)


interpretation skew_heap: Priority_Queue_Merge
where empty = Leaf and is_empty = "\<lambda>h. h = Leaf"
and merge = merge and insert = insert
and del_min = del_min and get_min = get_min
and invar = heap and mset = mset_tree
proof(standard, goal_cases)
  case 1 show ?case by simp
next
  case (2 q) show ?case by (cases q) auto
next
  case 3 show ?case by(simp add: mset_insert)
next
  case 4 show ?case by(rule mset_del_min)
next
  case 5 thus ?case using get_min mset_tree.simps(1) by blast
next
  case 6 thus ?case by(simp)
next
  case 7 thus ?case by(simp add: heap_insert)
next
  case 8 thus ?case by(simp add: heap_del_min)
next
  case 9 thus ?case by(simp add: mset_merge)
next
  case 10 thus ?case by(simp add: heap_merge)
qed


end
