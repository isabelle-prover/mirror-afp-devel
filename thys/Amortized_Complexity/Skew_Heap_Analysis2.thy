section{* Amortized Analysis of Skew Heaps *}

theory Skew_Heap_Analysis2
imports
  "../Skew_Heap/Skew_Heap"
  Amortized_Framework
  Priority_Queue_ops_meld2
begin

text{* The following proof is a simplified version of the one by Kaldewaij and
Schoenmakers~\cite{KaldewaijS-IPL91}. *}

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

corollary Glog: "G h \<le> log 2 (size1 h)"
by (metis Gexp le_log2_of_power size1_def)

lemma Dexp: "2 ^ D h \<le> size h + 1"
by (induction h) auto

corollary Dlog: "D h \<le> log 2 (size1 h)"
by (metis Dexp le_log2_of_power size1_def)

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


fun \<Phi> :: "'a heap \<Rightarrow> nat" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l _ r) = \<Phi> l + \<Phi> r + (if size l < size r then 1 else 0)"

corollary amor_eq: "t\<^sub>m\<^sub>e\<^sub>l\<^sub>d2 t1 t2 + \<Phi>(meld2 t1 t2) - \<Phi> t1 - \<Phi> t2 =
  G(meld2 t1 t2) + D t1 + D t2 + 1"
apply(induction t1 t2 rule: meld2.induct)
apply(auto simp: max_def)  (*slow*)
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
   3 * log 2 (size1 t1 + size1 t2) + 1" (is "?l \<le> _")
proof -
  have "?l \<le> G(meld t1 t2) + D t1 + D t2 + 1" using amor_le[of t1 t2] by arith
  also have "\<dots> = real(G(meld t1 t2)) + D t1 + D t2 + 1" by simp
  also have "\<dots> = real(G(meld t1 t2)) + (real(D t1) + D t2) + 1" by simp
  also have "D t1 \<le> log 2 (size1 t1)" by(rule Dlog)
  also have "D t2 \<le> log 2 (size1 t2)" by(rule Dlog)
  also have "G (meld t1 t2) \<le> log 2 (size1(meld t1 t2))" by(rule Glog)
  also have "size1(meld t1 t2) = size1 t1 + size1 t2 - 1" by(simp add: size1_def)
  also have "log 2 (size1 t1 + size1 t2 - 1) \<le> log 2 (size1 t1 + size1 t2)" by(simp add: size1_def)
  also have "log 2 (size1 t1) + log 2 (size1 t2) \<le> 2 * log 2 (real(size1 t1) + (size1 t2))"
    by(rule plus_log_le_2log_plus) (auto simp: size1_def)
  finally show ?thesis by(simp)
qed

fun exec :: "'a::linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a heap list \<Rightarrow> 'a heap" where
"exec Empty [] = Leaf" |
"exec (Insert a) [h] = Skew_Heap.insert a h" |
"exec Del_min [h] = del_min h" |
"exec Meld [h1,h2] = meld h1 h2"

fun cost :: "'a::linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a heap list \<Rightarrow> nat" where
"cost Empty [] = 1" |
"cost (Insert a) [h] = t\<^sub>m\<^sub>e\<^sub>l\<^sub>d (Node Leaf a Leaf) h + 1" |
"cost Del_min [h] = (case h of Leaf \<Rightarrow> 1 | Node t1 a t2 \<Rightarrow> t\<^sub>m\<^sub>e\<^sub>l\<^sub>d t1 t2 + 1)" |
"cost Meld [h1,h2] = t\<^sub>m\<^sub>e\<^sub>l\<^sub>d h1 h2 + 1"

fun U where
"U Empty [] = 1" |
"U (Insert _) [h] = 3 * log 2 (size1 h + 2) + 2" |
"U Del_min [h] = 3 * log 2 (size1 h + 2) + 4" |
"U Meld [h1,h2] = 3 * log 2 (size1 h1 + size1 h2) + 2"

interpretation Amortized
where arity = arity and exec = exec and inv = "\<lambda>_. True"
and cost = cost and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by simp
next
  case (3 f) thus ?case by(cases f)(auto)
next
  case (4 ss f)
  show ?case
  proof (cases f)
    case Empty thus ?thesis using 4(2) by (auto)
  next
    case [simp]: (Insert a)
    obtain h where [simp]: "ss = [h]" using 4(2) by (auto)
    thus ?thesis using a_meld_ub[of "Node Leaf a Leaf" "h"]
      by (simp add: numeral_eq_Suc insert_def)
  next
    case [simp]: Del_min
    obtain h where [simp]: "ss = [h]" using 4(2) by (auto)
    thus ?thesis
    proof (cases h)
      case Leaf with Del_min show ?thesis by simp
    next
      case (Node t1 _ t2)
      have [arith]: "log 2 (2 + (real (size t1) + real (size t2))) \<le>
               log 2 (4 + (real (size t1) + real (size t2)))" by simp
      from Del_min Node show ?thesis using a_meld_ub[of t1 t2]
        by (simp add: size1_def)
    qed
  next
    case [simp]: Meld
    obtain h1 h2 where [simp]: "ss = [h1,h2]" using 4(2) by (auto simp: numeral_eq_Suc)
    have [arith]: "log 2 (2 + (real (size h1) + real (size h2))) \<le>
                   log 2 (4 + (real (size h1) + real (size h2)))" by simp
      show ?thesis using a_meld_ub[of h1 h2] by (simp add: size1_def)
  qed
qed

end
