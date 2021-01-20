subsection \<open>Optimal Binary Search Trees\<close>

text \<open>
The material presented in this section just contains a simple and non-optimal version
(cubic instead of quadratic in the number of keys).
It can now be viewed to be superseded by the AFP entry \<open>Optimal_BST\<close>.
It is kept here as a more easily understandable example and for archival purposes.
\<close>

theory OptBST
imports
  "HOL-Library.Tree"
  "HOL-Library.Code_Target_Numeral"
  "../state_monad/State_Main" 
  "../heap_monad/Heap_Default"
  Example_Misc
  "HOL-Library.Product_Lexorder"
  "HOL-Library.RBT_Mapping"
begin

subsubsection \<open>Function \<open>argmin\<close>\<close>

text \<open>Function \<open>argmin\<close> iterates over a list and returns the rightmost element
that minimizes a given function:\<close>

fun argmin :: "('a \<Rightarrow> ('b::linorder)) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"argmin f (x#xs) =
  (if xs = [] then x else
   let m = argmin f xs in if f x < f m then x else m)"

text \<open>Note that @{term arg_min_list} is similar but returns the leftmost element.\<close>

lemma argmin_forall: "xs \<noteq> [] \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> P x) \<Longrightarrow> P (argmin f xs)"
by(induction xs) (auto simp: Let_def)

lemma argmin_Min: "xs \<noteq> [] \<Longrightarrow> f (argmin f xs) = Min (f ` set xs)"
by(induction xs) (auto simp: min_def intro!: antisym)


subsubsection \<open>Misc\<close>

lemma upto_join: "\<lbrakk> i \<le> j; j \<le> k \<rbrakk> \<Longrightarrow> [i..j-1] @ j # [j+1..k] = [i..k]"
  using upto_rec1 upto_split1 by auto

subsubsection \<open>Definitions\<close>

context
fixes W :: "int \<Rightarrow> int \<Rightarrow> nat"
begin

fun wpl :: "int \<Rightarrow> int \<Rightarrow> int tree \<Rightarrow> nat" where
   "wpl i j Leaf = 0"
 | "wpl i j (Node l k r) = wpl i (k-1) l + wpl (k+1) j r + W i j"

function min_wpl :: "int \<Rightarrow> int \<Rightarrow> nat" where
"min_wpl i j =
  (if i > j then 0
   else min_list (map (\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + W i j) [i..j]))"
  by auto
termination by (relation "measure (\<lambda>(i,j) . nat(j-i+1))") auto
declare min_wpl.simps[simp del]

function opt_bst :: "int * int \<Rightarrow> int tree" where
"opt_bst (i,j) =
  (if i > j then Leaf else argmin (wpl i j) [\<langle>opt_bst (i,k-1), k, opt_bst (k+1,j)\<rangle>. k \<leftarrow> [i..j]])"
  by auto
termination by (relation "measure (\<lambda>(i,j) . nat(j-i+1))") auto
declare opt_bst.simps[simp del]


subsubsection \<open>Functional Memoization\<close>

context
  fixes n :: nat
begin

context fixes
  mem :: "nat option array"
begin

memoize_fun min_wpl\<^sub>T: min_wpl
  with_memory dp_consistency_heap_default where bound = "Bound (0, 0) (int n, int n)" and mem="mem"
  monadifies (heap) min_wpl.simps

context includes heap_monad_syntax begin
thm min_wpl\<^sub>T'.simps min_wpl\<^sub>T_def
end

memoize_correct
  by memoize_prover

lemmas memoized_empty = min_wpl\<^sub>T.memoized_empty

end (* Fixed array *)

context
  includes heap_monad_syntax
  notes [simp del] = min_wpl\<^sub>T'.simps
begin

definition "min_wpl\<^sub>h \<equiv> \<lambda> i j. Heap_Monad.bind (mem_empty (n * n)) (\<lambda> mem. min_wpl\<^sub>T' mem i j)"

lemma min_wpl_heap:
  "min_wpl i j = result_of (min_wpl\<^sub>h i j) Heap.empty"
  unfolding min_wpl\<^sub>h_def
  using memoized_empty[of _ "\<lambda> m. \<lambda> (a, b). min_wpl\<^sub>T' m a b" "(i, j)", OF min_wpl\<^sub>T.crel]
  by (simp add: index_size_defs)

end

end (* Bound *)

context includes state_monad_syntax begin

memoize_fun min_wpl\<^sub>m: min_wpl with_memory dp_consistency_mapping monadifies (state) min_wpl.simps
thm min_wpl\<^sub>m'.simps

memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = min_wpl\<^sub>m.memoized_correct

memoize_fun opt_bst\<^sub>m: opt_bst with_memory dp_consistency_mapping monadifies (state) opt_bst.simps
thm opt_bst\<^sub>m'.simps

memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = opt_bst\<^sub>m.memoized_correct

end


subsubsection \<open>Correctness Proof\<close>

lemma min_wpl_minimal:
  "inorder t = [i..j] \<Longrightarrow> min_wpl i j \<le> wpl i j t"
proof(induction i j t rule: wpl.induct)
  case (1 i j)
  then show ?case by (simp add: min_wpl.simps)
next
  case (2 i j l k r)
  then show ?case 
  proof cases
    assume "i > j" thus ?thesis by(simp add: min_wpl.simps)
  next
    assume [arith]: "\<not> i > j"
    have kk_ij: "k\<in>set[i..j]" using 2 
        by (metis set_inorder tree.set_intros(2))
        
    let ?M = "((\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + W i j) ` {i..j})"
    let ?w = "min_wpl i (k-1) + min_wpl (k+1) j + W i j"
 
    have aux_min:"Min ?M \<le> ?w"
    proof (rule Min_le)
      show "finite ?M" by simp
      show "?w \<in> ?M" using kk_ij by auto
    qed

    have"inorder \<langle>l,k,r\<rangle> = inorder l @k#inorder r" by auto
    from this have C:"[i..j] = inorder l @ k#inorder r" using 2 by auto
    have D: "[i..j] = [i..k-1]@k#[k+1..j]" using kk_ij upto_rec1 upto_split1
      by (metis atLeastAtMost_iff set_upto) 

    have l_inorder: "inorder l = [i..k-1]"
      by (smt C D append_Cons_eq_iff atLeastAtMost_iff set_upto)
    have r_inorder: "inorder r = [k+1..j]" 
      by (smt C D append_Cons_eq_iff atLeastAtMost_iff set_upto)

    have "min_wpl i j = Min ?M" by (simp add: min_wpl.simps min_list_Min)
    also have "... \<le> ?w" by (rule aux_min)    
    also have "... \<le> wpl i (k-1) l + wpl (k+1) j r + W i j" using l_inorder r_inorder "2.IH" by simp
    also have "... = wpl i j \<langle>l,k,r\<rangle>" by simp
    finally show ?thesis .
  qed
qed

lemma opt_bst_correct: "inorder (opt_bst (i,j)) = [i..j]"
  by (induction "(i,j)" arbitrary: i j rule: opt_bst.induct)
     (clarsimp simp: opt_bst.simps upto_join | rule argmin_forall)+

lemma wpl_opt_bst: "wpl i j (opt_bst (i,j)) = min_wpl i j"
proof(induction i j rule: min_wpl.induct)
  case (1 i j)
  show ?case
  proof cases
    assume "i > j" thus ?thesis by(simp add: min_wpl.simps opt_bst.simps)
  next
    assume *[arith]: "\<not> i > j"
    let ?ts = "[\<langle>opt_bst (i,k-1), k, opt_bst (k+1,j)\<rangle>. k <- [i..j]]"
    let ?M = "((\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + W i j) ` {i..j})"
    have "?ts \<noteq> []" by (auto simp add: upto.simps)
    have "wpl i j (opt_bst (i,j)) = wpl i j (argmin (wpl i j) ?ts)" by (simp add: opt_bst.simps)
    also have "\<dots> = Min (wpl i j ` (set ?ts))" by (rule argmin_Min[OF \<open>?ts \<noteq> []\<close>])
    also have "\<dots> = Min ?M"
    proof (rule arg_cong[where f=Min])
      show "wpl i j ` (set ?ts) = ?M"
        by (fastforce simp: Bex_def image_iff 1[OF *])
    qed
    also have "\<dots> = min_wpl i j" by (simp add: min_wpl.simps min_list_Min)
    finally show ?thesis .
  qed
qed

lemma opt_bst_is_optimal:
  "inorder t = [i..j] \<Longrightarrow> wpl i j (opt_bst (i,j)) \<le> wpl i j t"
  by (simp add: min_wpl_minimal wpl_opt_bst)

end (* Weight function *)


subsubsection \<open>Test Case\<close>

text \<open>Functional Implementations\<close>

value "min_wpl (\<lambda>i j. nat(i+j)) 0 4"

value "opt_bst (\<lambda>i j. nat(i+j)) (0, 4)"


text \<open>Imperative Implementation\<close>

code_thms min_wpl

definition "min_wpl_test = min_wpl\<^sub>h (\<lambda>i j. nat(i+j)) 4 0 4"

code_reflect Test functions min_wpl_test

ML \<open>Test.min_wpl_test ()\<close>

end