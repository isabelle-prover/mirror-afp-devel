(* Author: Tobias Nipkow *)

subsection \<open>Okasaki's Pairing Heaps via Tree Potential\<close>

theory Pairing_Heap_List1_Analysis1
imports
  Pairing_Heap_List1_Analysis
  "HOL-Library.Tree_Multiset"
begin

text\<open>This theory analyses Okasaki heaps by defining the potential as a composition of
mapping the heaps to trees and the standard tree potential.\<close>

datatype_compat heap (* quickcheck *)


subsubsection \<open>Analysis\<close>

fun trees :: "'a heap list \<Rightarrow> 'a tree" where
"trees [] = Leaf" |
"trees (Hp x lhs # rhs) = Node (trees lhs) x (trees rhs)"

fun tree :: "'a heap \<Rightarrow> 'a tree" where
"tree heap.Empty = Leaf" |
"tree (Hp x hs) = (Node (trees hs) x Leaf)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
  "\<Phi> Leaf = 0"
| "\<Phi> (Node l x r) = log 2 (size (Node l x r)) + \<Phi> l + \<Phi> r"

abbreviation \<Phi>' :: "'a heap \<Rightarrow> real" where
"\<Phi>' h \<equiv> \<Phi>(tree h)"

abbreviation \<Phi>'' :: "'a heap list \<Rightarrow> real" where
"\<Phi>'' hs \<equiv> \<Phi>(trees hs)"

lemma \<Phi>''_ge0: "no_Emptys hs \<Longrightarrow> \<Phi>'' hs \<ge> 0"
by (induction hs rule: trees.induct) auto

abbreviation "size' h \<equiv> size(tree h)"
abbreviation "size'' hs \<equiv> size(trees hs)"

lemma \<Delta>\<Phi>_insert: "is_root hp \<Longrightarrow> \<Phi>' (insert x hp) - \<Phi>' hp \<le> log 2  (size' hp + 1)"
by(cases hp)(simp_all)

lemma \<Delta>\<Phi>_merge:
  "\<Phi>' (merge h1 h2) - \<Phi>' h1 - \<Phi>' h2 \<le> log 2 (size' h1 + size' h2 + 1) + 1"
proof(induction h1 h2 rule: merge.induct)
  case (3 x hsx y hsy)
  thus ?case
    using ld_le_2ld[of "size'' hsx" "size'' hsy"]
      log_le_cancel_iff[of 2 "size'' hsx + size'' hsy + 2" "size'' hsx + size'' hsy + 3"]
    by (auto simp: simp del: log_le_cancel_iff)
qed (auto)

lemma no_EmptyD: "no_Empty h \<Longrightarrow> \<exists>x hs. h = Hp x hs"
by(cases h)auto

lemma size_trees_pass\<^sub>1: "no_Emptys hs \<Longrightarrow> size''(pass\<^sub>1 hs) =  size'' hs"
by (induct hs rule: pass\<^sub>1.induct) (auto dest!: no_EmptyD)

lemma \<Delta>\<Phi>_pass1: "no_Emptys hs \<Longrightarrow> \<Phi>'' (pass\<^sub>1 hs) - \<Phi>'' hs  \<le> 2 * log 2 (size'' hs + 1) - length hs + 2"
proof (induction hs rule: pass\<^sub>1.induct)
  case (1 h1 h2 hs)
  let ?h12s = "h1 # h2 # hs" let ?m = "size'' hs"
  from "1.prems" obtain x1 hs1 x2 hs2 where h12: "h1 = Hp x1 hs1" "h2 = Hp x2 hs2"
    by (meson list.set_intros(1,2) no_Empty.elims(2))
  let ?n1 = "size'' hs1" let ?n2 = "size'' hs2"
  have "\<Phi>'' (pass\<^sub>1 ?h12s) - \<Phi>'' ?h12s =  \<Phi>'' (pass\<^sub>1 hs) + log 2 (?n1+?n2+1) - \<Phi>'' hs - log 2 (?n2+?m+1)" 
    using "1.prems" by (simp add: h12 size_trees_pass\<^sub>1)
  also have "\<dots> \<le> log 2 (?n1+?n2+1) - log 2 (?n2+?m+1) + 2 * log 2 (?m+1) - length hs + 2" 
    using 1 by (simp)
  also have "\<dots> \<le> 2 * log 2 (?n1+?n2+?m+2) - log 2 (?n2+?m+1) + log 2 (?m+1) - length hs" 
        using ld_sum_inequality [of "?n1+?n2+1" "?m + 1"] by(simp)
  also have "\<dots> \<le> 2 * log 2 (?n1+?n2+?m+2) - length hs" by simp
  also have "\<dots> = 2 * log 2 (size'' ?h12s) - length ?h12s + 2" using h12 by simp
  also have "\<dots> \<le> 2 * log 2 (size'' ?h12s + 1) - length ?h12s + 2" using h12 by simp
  finally show ?case .
qed simp_all

lemma pass\<^sub>2_struct: "no_Empty h \<Longrightarrow> \<exists>x hs'. pass\<^sub>2 (h # hs) = Hp x hs'"
by (smt (verit) merge.elims pass\<^sub>2.simps(2) no_EmptyD)

lemma size'_merge: "size' (merge (Hp x hs1) h2) = size'(Hp x hs1) + size' h2"
by(cases h2) auto

lemma size_pass\<^sub>2: "no_Emptys hs \<Longrightarrow> size' (pass\<^sub>2 hs) = size'' hs"
by (induction hs) (auto dest!: no_EmptyD simp: size'_merge)

lemma \<Delta>\<Phi>_pass2: "hs \<noteq> [] \<Longrightarrow> no_Emptys hs \<Longrightarrow> \<Phi>' (pass\<^sub>2 hs) - \<Phi>'' hs \<le> log 2 (size'' hs)"
proof (induction hs)
  case (Cons h1 hs)
  then obtain x hs1 where [simp]: "h1 = Hp x hs1"
    by (auto dest: no_EmptyD)
  show ?case 
  proof (cases hs)
    case [simp]: (Cons h2 hs2)
    obtain hs3 a where 2: "pass\<^sub>2 hs = Hp a hs3" 
      using pass\<^sub>2_struct Cons.prems(2) by fastforce
    hence 3: "size'' hs = size' \<dots>" using size_pass\<^sub>2 Cons.prems(2) by (metis list.set_intros(2)) 
    have link: "\<Phi>' (merge h1 (pass\<^sub>2 hs)) - \<Phi>'' hs1 - \<Phi>' (pass\<^sub>2 hs) =
          log 2 (size'' hs1 + size'' hs + 1) + log 2 (size'' hs1 + size'' hs) - log 2 (size'' hs)"
      using 2 3 \<open>h1 = _\<close> by simp
    have "\<Phi>' (pass\<^sub>2 (h1#hs)) - \<Phi>'' (h1#hs) =
        \<Phi>' (merge h1 (pass\<^sub>2 hs)) - \<Phi>'' hs1 - \<Phi>'' hs - log 2 (size'' hs1 + size'' hs + 1)"
      by (simp)
    also have "\<dots> = \<Phi>' (pass\<^sub>2 hs) - \<Phi>'' hs + log 2 (size'' hs1 + size'' hs) - log 2 (size'' hs)"
      using link by linarith
    also have "\<dots> \<le> log 2 (size'' hs1 + size'' hs)"
      using Cons.IH Cons.prems(2) by (simp)
    also have "\<dots> \<le> log 2 (size'' (h1#hs))" using 3 by auto
    finally show ?thesis .
  qed simp
qed simp

lemma trees_not_Leaf: "hs \<noteq> [] \<Longrightarrow> no_Emptys hs \<Longrightarrow> trees hs \<noteq> Leaf"
using trees.elims by force

corollary \<Delta>\<Phi>_pass2': assumes "no_Emptys hs"
shows "\<Phi>' (pass\<^sub>2 hs) - \<Phi>'' hs \<le> log 2 (size'' hs + 1)"
proof (cases "hs = []")
  case False
  have "log 2 (size'' hs) \<le> log 2 (size'' hs + 1)"
    using trees_not_Leaf[OF False assms] of_nat_eq_0_iff by(fastforce intro!: log_mono)
  thus ?thesis using \<Delta>\<Phi>_pass2[OF False assms] by linarith
qed simp

lemma \<Delta>\<Phi>_del_min: assumes "no_Emptys hs"
shows "\<Phi>' (del_min (Hp x hs)) - \<Phi>' (Hp x hs) 
  \<le> 2 * log 2 (size'' hs + 1) - length hs + 2"
proof -
  have "\<Phi>' (del_min (Hp x hs)) - \<Phi>' (Hp x hs) =
        \<Phi>' (pass\<^sub>2 (pass\<^sub>1 hs)) - (log 2 (1 + real (size'' hs)) + \<Phi>'' hs)" by simp
  also have "\<dots> \<le> \<Phi>'' (pass\<^sub>1 hs) - \<Phi>'' hs"
    using \<Delta>\<Phi>_pass2' [OF no_Emptys_pass1[OF assms]]
    by(simp add: size_trees_pass\<^sub>1[OF assms])
  also have "\<dots> \<le> 2 * log 2 (size'' hs + 1) - length hs + 2" by(rule \<Delta>\<Phi>_pass1[OF assms])
  finally show ?thesis .
qed

subsubsection \<open>Putting it all together (boiler plate)\<close>

fun U :: "'a :: linorder op \<Rightarrow> 'a heap list \<Rightarrow> real" where
"U Empty _ = 0" |
"U (Insert a) [h] = log 2 (size' h + 1)" |
"U Del_min [h] = 2*log 2 (size' h + 1) + 4" |
"U Merge [h1,h2] = log 2 (size' h1 + size' h2 + 1) + 1"

interpretation pairing0: Amortized
where arity = arity and exec = exec and cost = cost and inv = "is_root"
and \<Phi> = \<Phi>' and U = U
proof (standard, goal_cases)
  case (1 ss f) show ?case
  proof (cases f)
    case Empty with 1 show ?thesis by simp
  next
    case Insert thus ?thesis using 1 by(auto simp: is_root_merge)
  next
    case Merge
    thus ?thesis using 1 by(auto simp: is_root_merge numeral_eq_Suc)
  next
    case [simp]: Del_min
    then obtain h where [simp]: "ss = [h]" using 1 by auto
    show ?thesis
    proof (cases h)
      case [simp]: (Hp _ hs)
      show ?thesis
      proof cases
        assume "hs = []" thus ?thesis by simp
      next
        assume "hs \<noteq> []" thus ?thesis
          using 1(1) no_Emptys_pass1 by (auto intro: is_root_pass2)
      qed
    qed simp
  qed
next
  case (2 s) thus ?case by (cases s) (auto simp: \<Phi>''_ge0)
next
  case (3 ss f) show ?case
  proof (cases f)
    case Empty with 3 show ?thesis by(auto)
  next
    case (Insert x)
    thus ?thesis using \<Delta>\<Phi>_insert 3 by (auto)
  next
    case [simp]: Del_min
    then obtain h where [simp]: "ss = [h]" using 3 by auto
    show ?thesis
    proof (cases h)
      case [simp]: (Hp x hs)
      have "T_pass\<^sub>2 (pass\<^sub>1 hs) + T_pass\<^sub>1 hs \<le> 2 + length hs"
        by (induct hs rule: pass\<^sub>1.induct) simp_all
      hence  "cost f ss \<le> \<dots>" by simp
      moreover have  "\<Phi>' (del_min h) - \<Phi>' h \<le> 2*log 2 (size' h + 1) - length hs + 2"
      proof (cases "hs = []")
        case False
        hence "\<Phi>' (del_min h) - \<Phi>' h \<le> 2*log 2 (size' h) - length hs + 2"
          using  \<Delta>\<Phi>_del_min[of hs x] 3(1) by simp
        also have "\<dots> \<le> 2*log 2 (size' h + 1) - length hs + 2"
          by fastforce
        finally show ?thesis .
      qed simp
      ultimately show ?thesis by simp
    qed simp
  next
    case [simp]: Merge
    then obtain h1 h2 where [simp]: "ss = [h1, h2]"
      using 3 by(auto simp: numeral_eq_Suc)
    show ?thesis
    proof (cases "h1 = heap.Empty \<or> h2 = heap.Empty")
      case True thus ?thesis by auto
    next                  
      case False
      then obtain x1 x2 hs1 hs2 where [simp]: "h1 = Hp x1 hs1" "h2 = Hp x2 hs2"
        by (meson hps.cases) 
      have "\<Phi>' (merge h1 h2) - \<Phi>' h1 - \<Phi>' h2 \<le> log 2 (size' h1 + size' h2 + 1) + 1"
        using \<Delta>\<Phi>_merge[of h1 h2] by simp
      thus ?thesis by(simp)
    qed
  qed
qed

end
