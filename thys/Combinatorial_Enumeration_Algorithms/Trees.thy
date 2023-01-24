section "Trees"

theory Trees
imports
    "HOL-Library.Tree"
    Common_Lemmas
    (* "Catalan_Numbers.Catalan_Numbers" very big *)
begin

subsection"Definition"

text \<open>The set of trees can be defined with the pre-existing @{term "tree"} datatype:\<close>
definition trees :: "nat \<Rightarrow> unit tree set" where
  "trees n = {t. size t = n}"

text "Cardinality: \<open>Catalan number of n\<close>"
text "Example: \<open>trees 0 = {Leaf}\<close>"

(*algorithm and cardinality proofs taken from what Tobias Nipkow send me*)

subsection"Algorithm"
fun tree_enum :: "nat \<Rightarrow> unit tree list" where
"tree_enum 0 = [Leaf]" |
"tree_enum (Suc n) = [\<langle>t1, (), t2\<rangle>. i \<leftarrow> [0..<Suc n], t1 \<leftarrow> tree_enum i, t2 \<leftarrow> tree_enum (n-i)]"

subsection"Verification"

subsubsection"Cardinality"

lemma length_tree_enum:
  "length (tree_enum(Suc n)) = (\<Sum>i\<le>n. length(tree_enum i) * length(tree_enum (n - i)))"
  by (simp add: length_concat comp_def sum_list_triv atLeast_upt interv_sum_list_conv_sum_set_nat
         flip: lessThan_Suc_atMost)
(*
lemma "length (tree_enum n) = catalan n"
apply(induction n rule: catalan.induct)
apply(auto simp: length_tree_enum catalan_Suc simp del: upt_Suc tree_enum.simps(2))
done
*)

subsubsection"Correctness"

lemma tree_enum_correct1: "t \<in> set (tree_enum n) \<Longrightarrow> size t = n"
  by (induct n arbitrary: t rule: tree_enum.induct) (simp, fastforce)

lemma tree_enum_correct2: "n = size t \<Longrightarrow> t \<in> set (tree_enum n)"
proof (induct n arbitrary: t rule: tree_enum.induct)
  case 1
  then show ?case by simp
next
  case (2 n)
  show ?case proof(cases t)
    case Leaf
    then show ?thesis
      by (simp add: "2.prems") 
  next
    case (Node l e r)

    have i1: "(size l) < Suc n" using "2.prems" Node by auto
    have i2: "(size r) < Suc n" using "2.prems" Node by auto 

    have t1: "l \<in> set (tree_enum (size l))"
      apply(rule "2.hyps"(1) [of "(size l)"])
      using i1 by auto

    have t2: "r \<in> set (tree_enum (size r))"
      apply(rule "2.hyps"(1) [of "(size r)"])
      using i2 by auto

    have "\<langle>l, (), r\<rangle> \<notin> (\<lambda>t1. \<langle>t1, (), \<langle>\<rangle>\<rangle>) ` set (tree_enum (size l + size r)) \<Longrightarrow>
        \<exists>x\<in>{0..<size l + size r}. \<exists>xa\<in>set (tree_enum x). \<langle>l, (), r\<rangle> \<in> Node xa () ` set (tree_enum (size l + size r - x))"
      using t1 t2 by fastforce
    then have "\<langle>l, e, r\<rangle> \<in> set (tree_enum (size \<langle>l, e, r\<rangle>))"
      by auto

    then show ?thesis
      using Node using "2.prems" by simp
  qed
qed

theorem tree_enum_correct: "set(tree_enum n) = trees n"
proof(standard)
  show "set (tree_enum n) \<subseteq> trees n"
    unfolding trees_def using tree_enum_correct1 by auto
next
  show "trees n \<subseteq> set (tree_enum n)"
    unfolding trees_def using tree_enum_correct2 by auto
qed

subsubsection"Distinctness"

lemma tree_enum_Leaf: "\<langle>\<rangle> \<in> set (tree_enum n) \<longleftrightarrow> (n = 0)"
  by(cases n) auto

lemma tree_enum_elem_injective: "n \<noteq> m \<Longrightarrow> x \<in> set (tree_enum n) \<Longrightarrow> y \<in> set (tree_enum m) \<Longrightarrow> x \<noteq> y"
  using tree_enum_correct1 by auto

lemma tree_enum_elem_injective2: "x \<in> set (tree_enum n) \<Longrightarrow> y \<in> set (tree_enum m) \<Longrightarrow> x = y \<Longrightarrow> n = m"
  using tree_enum_elem_injective by auto

lemma concat_map_Node_not_equal:
  "xs \<noteq> [] \<Longrightarrow> xs2 \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> ys2 \<noteq> [] \<Longrightarrow> 
  \<forall> x\<in> set xs. \<forall> y \<in> set ys . x \<noteq> y \<Longrightarrow> 
  [\<langle>l, (), r\<rangle>. l \<leftarrow> xs2, r \<leftarrow> xs] \<noteq> [\<langle>l, (), r\<rangle>. l \<leftarrow> ys2, r \<leftarrow> ys]"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case proof(induct ys)
    case Nil
    then show ?case by simp
  next
    case (Cons y ys)
    obtain x2 x2s where o1: "xs2 = x2 # x2s"
      by (meson Cons.prems(3) neq_Nil_conv)
    obtain y2 y2s where o2: "ys2 = y2 # y2s"
      by (meson Cons.prems(5) neq_Nil_conv)

    have "[\<langle>l, (), r\<rangle>. l \<leftarrow> x2#x2s, r \<leftarrow> x # xs] \<noteq> [\<langle>l, (), r\<rangle>. l \<leftarrow> y2#y2s, r \<leftarrow> y # ys]"
      using Cons.prems(6) by auto
    then show ?case
      using o1 o2 by simp  
  qed
qed

lemma tree_enum_not_empty: "tree_enum n \<noteq> []"
  by(induct n) auto

lemma tree_enum_distinct_aux_outer:
  assumes "\<forall>i \<le> n. distinct (tree_enum i)"
  and "distinct xs"
  and "\<forall> i \<in> set xs. i < n"
  and "sorted_wrt (<) xs"
  shows "distinct (map (\<lambda>i. [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum i, r \<leftarrow> tree_enum (n-i)]) xs)"
using assms proof(induct xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have b1: "x < n" using Cons by auto

  have "\<forall> i \<in> set xs . x < i"
    using Cons.prems(4) strict_sorted_simps(2) by simp 
  then have "\<forall> i \<in> set xs . (n - i) < (n - x)"
    using b1 diff_less_mono2 by simp

  then have "\<forall> i \<in> set xs. \<forall> t1\<in> set (tree_enum (n - x)). \<forall> t2 \<in> set (tree_enum (n - i)) . t1 \<noteq> t2"
    using tree_enum_correct1 by (metis less_irrefl_nat) 
  then have 1: "\<forall> i \<in> set xs. [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum x, r \<leftarrow> tree_enum (n-x)] \<noteq>
          [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum i, r \<leftarrow> tree_enum (n-i)]"
    using concat_map_Node_not_equal tree_enum_not_empty by simp

  have 2: "distinct (map (\<lambda>i. [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum i, r \<leftarrow> tree_enum (n-i)]) xs)"
    using Cons by auto
    
  from 1 2 show ?case by auto
qed
  
lemma tree_enum_distinct_aux_left:
   "\<forall> i < n. distinct (tree_enum i) \<Longrightarrow> distinct ([\<langle>l, (), r\<rangle>. i \<leftarrow> [0..< n], l \<leftarrow> tree_enum i])"
proof(induct "n")
  case 0
  then show ?case by simp
next
  case (Suc n)
  have 1:"distinct (tree_enum n)"
    using Suc.prems by auto
  have 2: "distinct ([\<langle>l, (), r\<rangle>. i \<leftarrow> [0..< n], l \<leftarrow> tree_enum i])"
    using Suc by simp
  have 3: "distinct (map (\<lambda>l. \<langle>l, (), r\<rangle>) (tree_enum n))"
    using Node_left_distinct_map 1 by simp

  have 4: "\<lbrakk>\<And>t n. t \<in> set (tree_enum n) \<Longrightarrow> size t = n; m < n; y \<in> set (tree_enum n); y \<in> set (tree_enum m)\<rbrakk> \<Longrightarrow> False" for m y
    by blast
    
  from 1 2 3 4 tree_enum_correct1 show ?case
    by fastforce
qed

theorem tree_enum_distinct: "distinct(tree_enum n)"
proof(induct n rule: tree_enum.induct)
  case 1
  then show ?case by simp
next
  case (2 n)
  then have Ir: "i < Suc n \<Longrightarrow> distinct (tree_enum i)" for i
    by (metis atLeastLessThan_iff set_upt zero_le) 

  have c1: "distinct (concat (map (\<lambda>i. [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum i, r \<leftarrow> tree_enum (n-i)]) [0..<n]))"
  proof(rule distinct_concat)
    show "distinct (map (\<lambda>i. [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum i, r \<leftarrow> tree_enum (n-i)]) [0..<n])"
      apply(rule tree_enum_distinct_aux_outer)
      using Ir by auto
  next
    have "\<And>x. x < n \<Longrightarrow> distinct ([\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum x, r \<leftarrow> tree_enum (n-x)])"
      using Ir by (simp add: Node_right_distinct_concat_map)
    then show "\<And>ys. ys \<in> set (map (\<lambda>i. [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum i, r \<leftarrow> tree_enum (n-i)]) [0..<n]) \<Longrightarrow> distinct ys"
      by auto
  next
    have "\<lbrakk>[\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum x, r \<leftarrow> tree_enum (n-x)] \<noteq>
        [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum z, r \<leftarrow> tree_enum (n-z)];
        y \<in> set (tree_enum x); y \<in> set (tree_enum z)\<rbrakk>
       \<Longrightarrow> False" for x z y
      using tree_enum_elem_injective2 by auto
    then show  "\<And>ys zs.
       \<lbrakk>ys \<in> set (map (\<lambda>i. [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum i, r \<leftarrow> tree_enum (n-i)]) [0..<n]);
        zs \<in> set (map (\<lambda>i. [\<langle>l, (), r\<rangle>. l \<leftarrow> tree_enum i, r \<leftarrow> tree_enum (n-i)]) [0..<n]); ys \<noteq> zs\<rbrakk>
       \<Longrightarrow> set ys \<inter> set zs = {}"
      by fastforce
  qed

  have "distinct (tree_enum n)"
    using 2 by simp
  then have c2: "distinct (map (\<lambda>t1. \<langle>t1, (), \<langle>\<rangle>\<rangle>) (tree_enum n))"
    using Node_left_distinct_map by fastforce
  
  have c3: "\<And>xa xb. \<lbrakk>xa < n; xb \<in> set (tree_enum xa); xb \<in> set (tree_enum n); \<langle>\<rangle> \<in> set (tree_enum (n - xa))\<rbrakk> \<Longrightarrow> False"
    by (simp add: tree_enum_Leaf) 

  from c1 c2 c3 show ?case
    by fastforce
qed
end
