theory Skew_Heap
imports Complex_Main Amor "~~/src/HOL/Library/Tree"
begin

section "Skew Heap"

text{* Skew heaps were invented by Sleator and Tarjan~\cite{SleatorT-SIAM86}
but the proof is a simplified version of the one by Kaldewaij and
Schoenmakers~\cite{KaldewaijS-IPL91}. *}

subsection "Datatype"

type_synonym 'a heap = "'a tree"

fun rheavy :: "'a heap \<Rightarrow> bool" where
"rheavy(Node l _ r) = (size l < size r)"

fun rpath :: "'a heap \<Rightarrow> 'a heap list" where
"rpath Leaf = []" |
"rpath (Node l a r) = Node l a r # rpath r"

fun lpath :: "'a heap \<Rightarrow> 'a heap list" where
"lpath Leaf = []" |
"lpath (Node l a r) = Node l a r # lpath l"

fun G where
"G h = length(filter rheavy (lpath h))"

fun D where
"D h = length(filter (\<lambda>p. \<not> rheavy p) (rpath h))"

lemma Gexp: "2 ^ G h \<le> size h + 1"
by (induction h) auto

corollary Glog: "G h \<le> log 2 (size h + 1)"
proof -
  have "G h = log 2 (2 ^ G h)" by (simp add: log_nat_power)
  also have "log 2 (2 ^ G h) \<le> log 2 (size h + 1)"
    by(simp del: G.simps) (metis Gexp Suc_eq_plus1)
  finally show ?thesis .
qed

lemma Dexp: "2 ^ D h \<le> size h + 1"
by (induction h) auto

corollary Dlog: "D h \<le> log 2 (size h + 1)"
proof -
  have "D h = log 2 (2 ^ D h)" by (simp add: log_nat_power)
  also have "log 2 (2 ^ D h) \<le> log 2 (size h + 1)"
    by(simp del: D.simps) (metis Dexp Suc_eq_plus1)
  finally show ?thesis .
qed

subsubsection "Meld"

function meld :: "('a::linorder) heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"meld Leaf h = h" |
"meld h Leaf = h" |
"meld (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2 then Node (meld (Node l2 a2 r2) r1) a1 l1
    else Node (meld (Node l1 a1 r1) r2) a2 l2)" 
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

lemma meld_code: "meld h1 h2 =
  (case h1 of
   Leaf \<Rightarrow> h2 |
   Node l1 a1 r1 \<Rightarrow> (case h2 of
     Leaf \<Rightarrow> h1 |
     Node l2 a2 r2 \<Rightarrow> 
       (if a1 \<le> a2
        then Node (meld h2 r1) a1 l1
        else Node (meld h1 r2) a2 l2)))"
by(auto split: tree.split)

function meld2 :: "('a::linorder) heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"meld2 Leaf Leaf = Leaf" |
"meld2 Leaf (Node l2 a2 r2) = Node (meld2 r2 Leaf) a2 l2" |
"meld2 (Node l1 a1 r1) Leaf = Node (meld2 r1 Leaf) a1 l1" |
"meld2 (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2
    then Node (meld2 (Node l2 a2 r2) r1) a1 l1
    else Node (meld2 (Node l1 a1 r1) r2) a2 l2)"
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

function t\<^sub>m\<^sub>e\<^sub>l\<^sub>d :: "'a::linorder heap \<Rightarrow> 'a heap \<Rightarrow> nat" where
"t\<^sub>m\<^sub>e\<^sub>l\<^sub>d Leaf h = 1" |
"t\<^sub>m\<^sub>e\<^sub>l\<^sub>d h Leaf = 1" |
"t\<^sub>m\<^sub>e\<^sub>l\<^sub>d (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2 then t\<^sub>m\<^sub>e\<^sub>l\<^sub>d (Node l2 a2 r2) r1 else t\<^sub>m\<^sub>e\<^sub>l\<^sub>d (Node l1 a1 r1) r2) + 1"
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

function t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 :: "'a::linorder heap \<Rightarrow> 'a heap \<Rightarrow> nat" where
"t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 Leaf Leaf = 1" |
"t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 Leaf (Node l2 a2 r2) = t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 r2 Leaf + 1" |
"t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 (Node l1 a1 r1) Leaf = t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 r1 Leaf + 1" |
"t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 (Node l1 a1 r1) (Node l2 a2 r2) =
  (if a1\<le>a2 then t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 (Node l2 a2 r2) r1 else t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 (Node l1 a1 r1) r2) + 1"
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

lemma size_meld[simp]: "size(meld t1 t2) = size t1 + size t2"
by(induction t1 t2 rule: meld.induct) auto

lemma size_meld2[simp]: "size(meld2 t1 t2) = size t1 + size t2"
by(induction t1 t2 rule: meld2.induct) auto


subsection "Amortized Analysis"

fun \<Phi> :: "'a heap \<Rightarrow> nat" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l _ r) = \<Phi> l + \<Phi> r + (if size l < size r then 1 else 0)"

corollary amor_eq: "t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 t1 t2 + \<Phi>(meld2 t1 t2) - \<Phi> t1 - \<Phi> t2 =
  G(meld2 t1 t2) + D t1 + D t2 + 1"
apply(induction t1 t2 rule: meld2.induct)
apply(auto simp: max_def)
done

lemma plus_log_le_2log_plus: assumes [arith]: "x \<ge> 1" " y\<ge> 1" "b > 1"
shows "log b x + log b y \<le> 2 * log b (x + y)"
proof -
  have 1: "x*y \<le> (x+y)^2"
    by (simp add: numeral_eq_Suc algebra_simps add_increasing)
  have "log b x + log b y = log b (x * y)" by(simp add: log_mult assms)
  also have "\<dots> \<le> log b ((x+y)^2)" by (simp add: 1)
  finally show ?thesis by (simp add: log_nat_power)
qed

lemma amor_le:
  "t\<^sub>m\<^sub>e\<^sub>l\<^sub>d t1 t2 + \<Phi> (meld t1 t2) - \<Phi> t1 - \<Phi> t2 \<le>
   G(meld t1 t2) + D t1 + D t2 + 1"
apply(induction t1 t2 rule: meld.induct)
apply(auto split: if_splits)
done

lemma a_meld_ub:
  "t\<^sub>m\<^sub>e\<^sub>l\<^sub>d t1 t2 + \<Phi>(meld t1 t2) - \<Phi> t1 - \<Phi> t2 \<le>
   3 * log 2 (size t1 + size t2 + 2) + 1" (is "?l \<le> _")
proof -
  have "?l \<le> G(meld t1 t2) + D t1 + D t2 + 1" using amor_le[of t1 t2] by arith
  also have "\<dots> = real(G(meld t1 t2)) + D t1 + D t2 + 1" by simp
  also have "\<dots> = real(G(meld t1 t2)) + (real(D t1) + D t2) + 1" by simp
  also have "D t1 \<le> log 2 (size t1 + 1)" by(rule Dlog)
  also have "D t2 \<le> log 2 (size t2 + 1)" by(rule Dlog)
  also have "G (meld t1 t2) \<le> log 2 (size(meld t1 t2) + 1)" by(rule Glog)
  also have "size(meld t1 t2) = size t1 + size t2" by simp
  also have "log 2 (size t1 + size t2 + 1) \<le> log 2 (size t1 + size t2 + 2)" by simp
  also have "log 2 (size t1 + 1) + log 2 (size t2 + 1) \<le> 2 * log 2 (real(size t1 + 1) + (size t2 + 1))"
    by(rule plus_log_le_2log_plus) auto
  finally show ?thesis by(simp add: real_of_nat_Suc)
qed

datatype 'a op\<^sub>p\<^sub>q = Insert 'a | Delmin

fun nxt\<^sub>p\<^sub>q :: "'a::linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"nxt\<^sub>p\<^sub>q (Insert a) h = meld (Node Leaf a Leaf) h" |
"nxt\<^sub>p\<^sub>q Delmin h = (case h of Leaf \<Rightarrow> Leaf | Node t1 a t2 \<Rightarrow> meld t1 t2)"

fun t\<^sub>p\<^sub>q :: "'a::linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a heap \<Rightarrow> nat" where
"t\<^sub>p\<^sub>q (Insert a) h = t\<^sub>m\<^sub>e\<^sub>l\<^sub>d (Node Leaf a Leaf) h + 1" |
"t\<^sub>p\<^sub>q Delmin h = (case h of Leaf \<Rightarrow> 1 | Node t1 a t2 \<Rightarrow> t\<^sub>m\<^sub>e\<^sub>l\<^sub>d t1 t2 + 1)"


interpretation pq: amor
where init = "Leaf" and nxt = nxt\<^sub>p\<^sub>q
and inv = "\<lambda>_. True"
and t = t\<^sub>p\<^sub>q and \<Phi> = \<Phi>
and U = "\<lambda>f h. case f of
  Insert _ \<Rightarrow> 3 * log 2 (size h + 3) + 2 | Delmin \<Rightarrow> 3 * log 2 (size h + 3) + 4"
proof
  case goal1 show ?case by auto
next
  case goal2 thus ?case by auto
next
  case goal3 thus ?case by(simp)
next
  case goal4 show ?case by(simp)
next
  case goal5
  show ?case
  proof (cases f)
   case (Insert a)
   thus ?thesis using a_meld_ub[of "Node Leaf a Leaf" "s"]
     by (simp add: numeral_eq_Suc)
  next
    case Delmin
    thus ?thesis
    proof (cases s)
      case Leaf with Delmin show ?thesis by simp
    next
      case (Node t1 _ t2)
      have [arith]: "log 2 (2 + (real (size t1) + real (size t2))) \<le>
               log 2 (4 + (real (size t1) + real (size t2)))" by simp
      from Delmin Node show ?thesis using a_meld_ub[of t1 t2]
        by (simp add: real_of_nat_Suc)
    qed
  qed
qed

end
