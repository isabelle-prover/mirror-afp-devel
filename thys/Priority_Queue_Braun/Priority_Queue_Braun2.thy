section "Priority Queues Based on Braun Trees 2"

theory Priority_Queue_Braun2
imports Priority_Queue_Braun
begin

text \<open>This is the version verified by Jean-Christophe Filliâtre with the help of the Why3 system
\<^url>\<open>http://toccata.lri.fr/gallery/braun_trees.en.html\<close>.
Only the deletion function (\<open>del_min2\<close> below) differs from Paulson's version.
But the difference turns out to be minor --- see below.\<close>

(* TODO mv *)
lemma neq_Leaf_iff_size: "t \<noteq> Leaf \<longleftrightarrow> size t > 0"
by (simp add: zero_less_iff_neq_zero)


subsection "Function \<open>del_min2\<close>"

fun le_root :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> bool" where
"le_root a t = (t = Leaf \<or> a \<le> value t)"

fun replace_min :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"replace_min x (Node l _ r) =
  (if le_root x l & le_root x r then Node l x r
   else
     let a = value l in
     if le_root a r then Node (replace_min x l) a r
     else Node l (value r) (replace_min x r))"

fun merge :: "'a::linorder tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"merge l Leaf = l" |
"merge (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2 then Node (Node l2 a2 r2) a1 (merge l1 r1)
    else let (x, l') = del_left (Node l1 a1 r1)
         in Node (replace_min x (Node l2 a2 r2)) a2 l')"

fun del_min2 where
"del_min2 Leaf = Leaf" |
"del_min2 (Node l x r) = merge l r"


subsection "Correctness Proof"

text \<open>It turns out that @{const replace_min} is just @{const sift_down} in disguise:\<close>

lemma replace_min_sift_down: "braun (Node l a r) \<Longrightarrow> replace_min x (Node l a r) = sift_down l x r"
by(induction l x r rule: sift_down.induct)(auto)

text \<open>This means that @{const del_min2} is merely a slight optimization of @{const del_min}:
instead of calling @{const del_left} right away, @{const merge} can take advantage of the case
where the smaller element is at the root of the left heap and can be moved up without complications.
However, on average this is just the case on the first level.\<close>

lemma mset_tree_replace_min:
  "\<lbrakk> braun t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
  mset_tree(replace_min x t) = (mset_tree t - {#value t#}) + {#x#}"
by(auto simp add: mset_sift_down neq_Leaf_iff replace_min_sift_down simp del: replace_min.simps)
(* An explicit proof:
apply(induction t)
apply(auto simp: Let_def neq_Leaf_iff_size tree.set_sel(2))
done
*)

lemma braun_size_replace_min:
  "\<lbrakk> braun t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow> braun(replace_min x t) \<and> size(replace_min x t) = size t"
by(auto simp add: size_sift_down braun_sift_down neq_Leaf_iff replace_min_sift_down
        simp del: replace_min.simps)
(* An explicit proof:
apply(induction t)
apply(auto simp add: Let_def neq_Leaf_iff_size)
done
*)
(*
lemma heap_value_least: "\<lbrakk> heap t; x \<le> value t \<rbrakk>
       \<Longrightarrow> \<forall>a \<in> set_tree t. x \<le> a \<longleftrightarrow> True"
by (metis Min.boundedE empty_iff finite_set_tree get_min set_mset_tree tree.simps(14))
*)
lemma heap_replace_min:
  "\<lbrakk> braun t; heap t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow> heap(replace_min x t)"
by(auto simp add: heap_sift_down neq_Leaf_iff replace_min_sift_down simp del: replace_min.simps)
(* A long explicit proof:
proof(induction t)
  case Leaf thus ?case by simp
next
  case (Node l a r)
  have "braun l" "braun r" using Node.prems(1) by auto
  show ?case
  proof (cases "le_root x l & le_root x r")
    case True
    with Node(4) show ?thesis by(auto dest: heap_value_least)
  next
    case False
    hence "l \<noteq> Leaf" using Node.prems(1) by(auto)
    show ?thesis
    proof cases
      assume "le_root (value l) r"
      have "value l \<le> x" using False \<open>le_root (value l) r\<close> by auto
      moreover have "\<forall>a \<in># mset_tree l. value l \<le> a"
        using Node.prems(2) heap_value_least by auto
      ultimately have 1: "\<forall>a \<in> set_tree(replace_min x l). value l \<le> a"
        using mset_tree_replace_min[OF \<open>braun l\<close> \<open>l \<noteq> Leaf\<close>]
        by(auto simp flip: set_mset_tree dest: in_diffD)
      have "\<forall>a \<in> set_tree r. value l \<le> a"
        using Node.prems(2) \<open>le_root (value l) r\<close> heap_value_least by auto
      thus ?thesis
        using False \<open>le_root (value l) r\<close> \<open>l \<noteq> Leaf\<close> Node.IH(1)[OF \<open>braun l\<close>] Node.prems(2) 1
        by (auto)
    next
      assume "\<not> le_root (value l) r"
      hence "r \<noteq> Leaf" "le_root (value r) l" "value r \<le> x" using Node.prems(1) False by(auto)
      have "\<forall>a \<in># mset_tree r. value r \<le> a"
        using Node.prems(2) heap_value_least by auto
      with \<open>value r \<le> x\<close> have 1: "\<forall>a \<in> set_tree(replace_min x r). value r \<le> a"
        using mset_tree_replace_min[OF \<open>braun r\<close> \<open>r \<noteq> Leaf\<close>]
        by(auto simp flip: set_mset_tree dest: in_diffD)
      have "\<forall>x\<in>set_tree l. value r \<le> x"
        using Node.prems(2) \<open>le_root (value r) l\<close> heap_value_least by auto
      thus ?thesis
        using False \<open>\<not> le_root (value l) r\<close> \<open>l \<noteq> Leaf\<close> Node.IH(2)[OF \<open>braun r\<close>] Node.prems(2) 1
        by (auto)
    qed
  qed
qed
*)

text \<open>Function @{const merge}:\<close>

lemma mset_tree_merge:
  "braun (Node l x r) \<Longrightarrow> mset_tree(merge l r) = mset_tree l + mset_tree r"
by(induction l r rule: merge.induct)
  (auto simp: Let_def mset_tree_replace_min neq_Leaf_iff_size tree.set_sel(2)
        dest!: del_left_mset split!: prod.split)

lemma heap_merge:
  "\<lbrakk> braun (Node l x r); heap l; heap r \<rbrakk> \<Longrightarrow> heap(merge l r)"
proof(induction l r rule: merge.induct)
  case 1 thus ?case by simp
next
  case (2 l1 a1 r1 l2 a2 r2)
  show ?case
  proof cases
    assume "a1 \<le> a2"
    thus ?thesis using 2 by(auto simp: ball_Un mset_tree_merge simp flip: set_mset_tree)
  next
    assume "\<not> a1 \<le> a2"
    let ?l = "Node l1 a1 r1" let ?r = "Node l2 a2 r2"
    have "braun ?r" using "2.prems"(1) by auto
    obtain x l' where dl: "del_left ?l = (x, l')" by (metis surj_pair)
    from del_left_heap[OF this _ "2.prems"(2)] have "heap l'" by auto
    have hr: "heap(replace_min x ?r)" using heap_replace_min[OF \<open>braun ?r\<close> "2.prems"(3)] by simp
    have 0: "\<forall>x \<in> set_tree ?l. a2 \<le> x" using "2.prems"(2) \<open>\<not> a1 \<le> a2\<close> by (auto simp: ball_Un)
    moreover have "set_tree l' \<subseteq> set_tree ?l" "x \<in> set_tree ?l"
      using del_left_mset[OF dl] by (auto simp flip: set_mset_tree dest:in_diffD simp: union_iff)
    ultimately have 1: "\<forall>x \<in> set_tree l'. a2 \<le> x" by blast
    have "\<forall>x \<in> set_tree ?r. a2 \<le> x" using \<open>heap ?r\<close> by auto
    thus ?thesis
      using \<open>\<not> a1 \<le> a2\<close> dl \<open>heap(replace_min x ?r)\<close> \<open>heap l'\<close> \<open>x \<in> set_tree ?l\<close> 0 1
      by(auto simp: mset_tree_replace_min[OF \<open>braun ?r\<close>] simp flip: set_mset_tree
              simp del: replace_min.simps)
  qed
next
  case 3 thus ?case by simp
qed

lemma del_left_braun_size:
  "del_left t = (x,t') \<Longrightarrow> braun t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> braun t' \<and> size t = size t' + 1"
by (simp add: del_left_braun del_left_size)

lemma braun_size_merge:
  "braun (Node l x r) \<Longrightarrow> braun(merge l r) \<and> size(merge l r) = size l + size r"
apply(induction l r rule: merge.induct)
apply(auto simp: Let_def neq_Leaf_iff_size braun_size_replace_min
           dest!: del_left_braun_size split!: prod.split)
done


text \<open>Last step: prove all axioms of the priority queue specification:\<close>

interpretation braun: Priority_Queue
where empty = Leaf and is_empty = "\<lambda>h. h = Leaf"
and insert = insert and del_min = del_min2
and get_min = "value" and invar = "\<lambda>h. braun h \<and> heap h"
and mset = mset_tree
proof(standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by simp
next
  case 3 show ?case by(simp add: mset_insert)
next
  case 4 thus ?case by(auto simp: mset_tree_merge neq_Leaf_iff)
next
  case 5 thus ?case using get_min mset_tree.simps(1) by blast
next
  case 6 thus ?case by(simp)
next
  case 7 thus ?case by(simp add: heap_insert braun_insert)
next
  case 8 thus ?case by(auto simp: heap_merge braun_size_merge neq_Leaf_iff)
qed


end
