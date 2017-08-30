section "Skew Heap"

theory Skew_Heap_Analysis2
imports
  Skew_Heap_Analysis
  Amortized_Framework
  Priority_Queue_ops_merge
begin

lemma t_merge_nneg: "t_merge h1 h2 \<ge> 0"
by(induction h1 h2 rule: t_merge.induct) auto

fun exec :: "'a::linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a heap list \<Rightarrow> 'a heap" where
"exec Empty [] = Leaf" |
"exec (Insert a) [h] = Skew_Heap.insert a h" |
"exec Del_min [h] = del_min h" |
"exec Merge [h1,h2] = merge h1 h2"

fun cost :: "'a::linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a heap list \<Rightarrow> nat" where
"cost Empty [] = 1" |
"cost (Insert a) [h] = nat(t_merge (Node Leaf a Leaf) h)" |
"cost Del_min [h] = (case h of Leaf \<Rightarrow> 1 | Node t1 a t2 \<Rightarrow> nat(t_merge t1 t2))" |
"cost Merge [h1,h2] = nat(t_merge h1 h2)"

fun U where
"U Empty [] = 1" |
"U (Insert _) [h] = 3 * log 2 (size1 h + 2) + 1" |
"U Del_min [h] = 3 * log 2 (size1 h + 2) + 3" |
"U Merge [h1,h2] = 3 * log 2 (size1 h1 + size1 h2) + 1"

interpretation Amortized
where arity = arity and exec = exec and inv = "\<lambda>_. True"
and cost = cost and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case (2 h) show ?case using \<Phi>_nneg[of h] by linarith
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
    thus ?thesis using a_merge[of "Node Leaf a Leaf" "h"]
      by (simp add: numeral_eq_Suc insert_def rh_def of_nat_nat[OF t_merge_nneg])
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
      from Del_min Node show ?thesis using a_merge[of t1 t2]
        by (simp add: size1_def of_nat_nat[OF t_merge_nneg])
    qed
  next
    case [simp]: Merge
    obtain h1 h2 where "ss = [h1,h2]" using 4(2) by (auto simp: numeral_eq_Suc)
    thus ?thesis using a_merge[of h1 h2] by (simp add: of_nat_nat[OF t_merge_nneg])
  qed
qed

end
