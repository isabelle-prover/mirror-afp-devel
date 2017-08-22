section "Priority Queues Based on Braun Trees"

theory Priority_Queue_Braun
imports
  "HOL-Library.Tree_Multiset"
  "HOL-Library.Pattern_Aliases"
begin


subsection "Introduction"

text{* Braun, Rem and Hoogerwoord \cite{BraunRem,Hoogerwoord} used
specific balanced binary trees, often called Braun trees (where in
each node with subtrees $l$ and $r$, $size(r) \le size(l) \le
size(r)+1$), to implement flexible arrays. Paulson \cite{Paulson}
(based on code supplied by Okasaki)
implemented priority queues via Braun trees. This theory verifies
Paulsons's implementation, including the logarithmic bounds.  *}


subsection {* Braun predicate *}

fun braun :: "'a tree \<Rightarrow> bool" where
"braun Leaf = True" |
"braun (Node l x r) = (size r \<le> size l \<and> size l \<le> size r + 1 \<and> braun l \<and> braun r)"

lemma height_size_braun: "braun t \<Longrightarrow> 2 ^ (height t) \<le> 2 * size t + 1"
proof(induction t)
  case (Node t1)
  show ?case
  proof (cases "height t1")
    case 0 thus ?thesis using Node by simp
  next
    case (Suc n)
    hence "2 ^ n \<le> size t1" using Node by simp
    thus ?thesis using Suc Node by(auto simp: max_def)
  qed
qed simp


subsection {* Insertion *}

fun insert_pq :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert_pq a Leaf = Node Leaf a Leaf" |
"insert_pq a (Node l x r) =
 (if a < x then Node (insert_pq x r) a l else Node (insert_pq a r) x l)"

value "fold insert_pq [0::int,1,2,3,-55,-5] Leaf"

lemma size_insert_pq[simp]: "size(insert_pq x t) = size t + 1"
by(induction t arbitrary: x) auto

lemma mset_insert_pq[simp]: "mset_tree(insert_pq x t) = {#x#} + mset_tree t"
by(induction t arbitrary: x) (auto simp: ac_simps)

lemma set_insert_pq[simp]: "set_tree(insert_pq x t) = insert x (set_tree t)"
by(induction t arbitrary: x) auto

lemma braun_insert_pq: "braun t \<Longrightarrow> braun(insert_pq x t)"
by(induction t arbitrary: x) auto

lemma heap_insert_pq: "heap t \<Longrightarrow> heap(insert_pq x t)"
by(induction t arbitrary: x) (auto  simp add: ball_Un)


subsection {* Deletion *}

fun del_left :: "'a tree \<Rightarrow> 'a * 'a tree" where
"del_left (Node Leaf x Leaf) = (x,Leaf)" |
"del_left (Node l x r) = (let (y,l') = del_left l in (y,Node r x l'))"

lemma del_left_size:
  "del_left t = (x,t') \<Longrightarrow> braun t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> size t = size t' + 1"
apply(induction t arbitrary: x t' rule: del_left.induct)
apply(auto split: prod.splits)
by fastforce

lemma del_left_braun:
  "del_left t = (x,t') \<Longrightarrow> braun t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> braun t'"
apply(induction t arbitrary: x t' rule: del_left.induct)
apply(fastforce dest: del_left_size split: prod.splits)+
done

lemma del_left_elem:
  "del_left t = (x,t') \<Longrightarrow> braun t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> x \<in> set_tree t"
apply(induction t arbitrary: x t' rule: del_left.induct)
apply(fastforce split: prod.splits)+
done

lemma del_left_set:
  "del_left t = (x,t') \<Longrightarrow> braun t \<Longrightarrow> t \<noteq> Leaf
  \<Longrightarrow> set_tree t = insert x (set_tree t')"
apply(induction t arbitrary: x t' rule: del_left.induct)
apply(fastforce split: prod.splits)+
done

lemma del_left_mset:
  "del_left t = (x,t') \<Longrightarrow> braun t \<Longrightarrow> t \<noteq> Leaf
  \<Longrightarrow> mset_tree t' = mset_tree t - {#x#}"
proof (induction t arbitrary: x t' rule: del_left.induct)
  case 1 then show ?case by simp
next
  case "2_1" then show ?case
    by (auto simp: diff_union_swap ac_simps
     dest!: del_left_elem split: prod.splits)
next
  case ("2_2" l x v u w y t)
  from "2_2" obtain t' where t: "t = \<langle>\<langle>v, u, w\<rangle>, x, t'\<rangle>"
    by (auto split: prod.splits)
  from "2_2" have y: "y \<in># mset_tree l"
    by (auto dest!: del_left_elem split: prod.splits)
  then have "l \<noteq> \<langle>\<rangle>"  by auto
  with t "2_2.prems" "2_2.IH" [of y t']
    have "mset_tree t' = mset_tree l - {#y#}"
    by (auto simp: dest!: del_left_elem split: prod.splits)
  with y have "mset_tree l = mset_tree t' + {#y#}"
    by simp
  with t show ?case
    by (simp add: ac_simps multiset_diff_union_assoc)
next
  case 3 then show ?case by simp
qed

lemma del_left_heap:
  "del_left t = (x,t') \<Longrightarrow> heap t \<Longrightarrow> braun t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> heap t'"
proof(induction t arbitrary: x t' rule: del_left.induct)
  case ("2_1" ll a lr b r)
  from "2_1.prems"(1) obtain l' where
    "del_left (Node ll a lr) = (x,l')" and [simp]: "t' = Node r b l'"
    by(auto split: prod.splits)
  from del_left_set[OF this(1)] "2_1.IH"[OF this(1)] "2_1.prems"
  show ?case by(auto)
next
  case "2_2" thus ?case by(fastforce dest: del_left_set split: prod.splits)
next
qed auto

context includes pattern_aliases
begin

function (sequential) sift_down :: "'a::linorder tree \<Rightarrow> 'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"sift_down Leaf a Leaf = Node Leaf a Leaf" |
"sift_down (Node Leaf x Leaf) a Leaf =
  (if a \<le> x then Node (Node Leaf x Leaf) a Leaf
   else Node (Node Leaf a Leaf) x Leaf)" |
"sift_down (Node l1 x1 r1 =: t1) a (Node l2 x2 r2 =: t2) =
  (if a \<le> x1 \<and> a \<le> x2
   then Node t1 a t2
   else if x1 \<le> x2 then Node (sift_down l1 a r1) x1 t2
        else Node t1 x2 (sift_down l2 a r2))"
by pat_completeness auto
termination
by (relation "measure (%(l,a,r). size l + size r)") auto

end

lemma size_sift_down:
  "braun(Node l a r) \<Longrightarrow> size(sift_down l a r) = size l + size r + 1"
by(induction l a r rule: sift_down.induct) (auto simp: Let_def)

lemma braun_sift_down:
  "braun(Node l a r) \<Longrightarrow> braun(sift_down l a r)"
by(induction l a r rule: sift_down.induct) (auto simp: size_sift_down Let_def)

lemma mset_sift_down:
  "braun(Node l a r) \<Longrightarrow> mset_tree(sift_down l a r) = {#a#} + (mset_tree l + mset_tree r)"
by(induction l a r rule: sift_down.induct) (auto simp: ac_simps Let_def)

lemma set_sift_down: "braun(Node l a r)
  \<Longrightarrow> set_tree(sift_down l a r) = insert a (set_tree l \<union> set_tree r)"
by(drule arg_cong[where f=set_mset, OF mset_sift_down]) (simp)

lemma heap_sift_down:
  "braun(Node l a r) \<Longrightarrow> heap l \<Longrightarrow> heap r \<Longrightarrow> heap(sift_down l a r)"
by (induction l a r rule: sift_down.induct) (auto simp: set_sift_down ball_Un Let_def)

fun del_min :: "'a::linorder tree \<Rightarrow> 'a tree" where
"del_min Leaf = Leaf" |
"del_min (Node Leaf x r) = Leaf" |
"del_min (Node l x r) = (let (y,l') = del_left l in sift_down r y l')"

lemma braun_del_min: "braun t \<Longrightarrow> braun(del_min t)"
apply(cases t rule: del_min.cases)
  apply simp
 apply simp
apply (fastforce split: prod.split intro!: braun_sift_down
  dest: del_left_size del_left_braun)
done

lemma heap_del_min: "heap t \<Longrightarrow> braun t \<Longrightarrow> heap(del_min t)"
apply(cases t rule: del_min.cases)
  apply simp
 apply simp
apply (fastforce split: prod.split intro!: heap_sift_down
  dest: del_left_size del_left_braun del_left_heap)
done

lemma size_del_min: assumes "braun t" shows "size(del_min t) = size t - 1"
proof(cases t rule: del_min.cases)
  case [simp]: (3 ll b lr a r)
  { fix y l' assume "del_left (Node ll b lr) = (y,l')"
    hence "size(sift_down r y l') = size t - 1" using assms
    by(subst size_sift_down) (auto dest: del_left_size del_left_braun) }
  thus ?thesis by(auto split: prod.split)
qed (insert assms, auto)

lemma mset_del_min: assumes "braun t" "heap t" "t \<noteq> Leaf"
shows "mset_tree t = {#root_val t#} + mset_tree(del_min t)"
proof(cases t rule: del_min.cases)
  case 1 with assms show ?thesis by simp
next
  case 2 with assms show ?thesis by (simp)
next
  case [simp]: (3 ll b lr a r)
  { fix y l' assume del: "del_left (Node ll b lr) = (y,l')"
    have "mset_tree t = {#a#} + mset_tree(sift_down r y l')"
      using assms del_left_mset[OF del] del_left_size[OF del]
        del_left_braun[OF del]del_left_elem[OF del]
      apply (subst mset_sift_down)
      apply (auto simp: ac_simps)
      done }
  thus ?thesis by(auto split: prod.split)
qed

lemma set_del_min: "\<lbrakk> braun t; heap t; t \<noteq> Leaf \<rbrakk>
  \<Longrightarrow> set_tree t = insert (root_val t) (set_tree(del_min t))"
by(drule (2) arg_cong[where f=set_mset, OF mset_del_min]) (simp)


end
