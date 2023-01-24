section"Injectivity for two argument functions"

theory Common_Lemmas
  imports
  "HOL.List"
  "HOL-Library.Tree"
begin

text \<open>This section introduces @{term "inj2_on"} which generalizes @{term "inj_on"} on curried
functions with two arguments and contains subsequent theorems about such functions.\<close>

text"
We could use curried function directly with for example \<open>case_prod\<close>,
but this way the proofs become simpler and easier to read."
definition inj2_on :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "inj2_on f A B \<longleftrightarrow> (\<forall>x1\<in>A. \<forall>x2\<in>A. \<forall>y1\<in>B. \<forall>y2\<in>B. f x1 y1 = f x2 y2 \<longrightarrow> x1 = x2 \<and> y1 = y2)"

abbreviation inj2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> bool" where
  "inj2 f \<equiv> inj2_on f UNIV UNIV"

subsection \<open>Correspondence between @{term "inj2_on"} and @{term "inj_on"}\<close>

lemma inj2_curried: "inj2_on (curry f) A B \<longleftrightarrow> inj_on f (A\<times>B)"
  unfolding inj2_on_def inj_on_def by auto

lemma inj2_on_all: "inj2 f \<Longrightarrow> inj2_on f A B"
  unfolding inj2_on_def by simp

lemma inj2_inj_first: "inj2 f \<Longrightarrow> inj f"
  unfolding inj2_on_def inj_on_def by simp

lemma inj2_inj_second: "inj2 f \<Longrightarrow> inj (f x)"
  unfolding inj2_on_def inj_on_def by simp

lemma inj2_inj_second_flipped: "inj2 f \<Longrightarrow> inj (\<lambda>x. f x y)"
  unfolding inj2_on_def inj_on_def by simp


subsection"Proofs with inj2"

text\<open>Already existing for @{term "inj"}:\<close>
thm distinct_map

lemma inj2_on_distinct_map:
  assumes "inj2_on f {x} (set xs)"
  shows "distinct xs = distinct (map (f x) xs)"
  using assms distinct_map by (auto simp: inj2_on_def inj_onI)

lemma inj2_distinct_map:
  assumes "inj2 f"
  shows "distinct xs = distinct (map (f x) xs)"
  using assms inj2_on_distinct_map inj2_on_all by fast

lemma inj2_on_distinct_concat_map:
  assumes "inj2_on f (set xs) (set ys)"
  shows "\<lbrakk>distinct ys; distinct xs\<rbrakk> \<Longrightarrow> distinct [f x y. x \<leftarrow> xs, y \<leftarrow> ys]"
using assms proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have nin: "x \<notin> set xs"
    by simp

  then have "inj2_on f {x} (set ys)"
    using Cons unfolding inj2_on_def by simp
  then have 1: "distinct (map (f x) ys)"
    using Cons inj2_on_distinct_map by fastforce

  have 2: "distinct (concat (map (\<lambda>x. map (f x) ys) xs))"
    using Cons unfolding inj2_on_def by simp

  have 3: "\<lbrakk>xa \<in> set xs; xb \<in> set ys; f x xb = f xa xc; xc \<in> set ys\<rbrakk> \<Longrightarrow> False " for xa xb xc
    using Cons(4) unfolding inj2_on_def
    using nin by force 

  from 1 2 3 show ?case
    by auto
qed

lemma inj2_distinct_concat_map:
  assumes "inj2 f"
  shows "\<lbrakk>distinct ys; distinct xs\<rbrakk> \<Longrightarrow> distinct [f x y. x \<leftarrow> xs, y \<leftarrow> ys]"
  using assms inj2_on_all inj2_on_distinct_concat_map by blast

lemma inj2_distinct_concat_map_function:
  assumes "inj2 f"
  shows"\<lbrakk>\<forall> x \<in> set xs. distinct (g x); distinct xs\<rbrakk> \<Longrightarrow> distinct [f x y. x \<leftarrow> xs, y \<leftarrow> g x]"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have 1: "distinct (map (f x) (g x))"
    using Cons assms inj2_distinct_map by fastforce
    
  have 2: "distinct (concat (map (\<lambda>x. map (f x) (g x)) xs))"
    using Cons by simp
    
  have 3: "\<And>xa xb xc. \<lbrakk>xa \<in> set xs; xb \<in> set (g x); f x xb = f xa xc; xc \<in> set (g xa)\<rbrakk>
      \<Longrightarrow> False"
    using Cons assms unfolding inj2_on_def by auto 
    
   show ?case using 1 2 3 
    by auto
qed

lemma distinct_concat_Nil: "distinct (concat (map (\<lambda>y. []) xs))"
  by(induct xs) auto

lemma inj2_distinct_concat_map_function_filter:
  assumes "inj2 f"
  shows"\<lbrakk>\<forall> x \<in> set xs. distinct (g x); distinct xs\<rbrakk> \<Longrightarrow> distinct [f x y. x \<leftarrow> xs, y \<leftarrow> g x, h x]"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have 1: "distinct (map (f x) (g x))"
    using Cons assms inj2_distinct_map by fastforce
    
  have 2: "distinct (concat (map (\<lambda>x. concat (map (\<lambda>y. if h x then [f x y] else []) (g x))) xs))"
    using Cons by simp

  have 3: "\<And>xa xb xc.
       \<lbrakk>h x; xa \<in> set (g x); xb \<in> set xs; f x xa = f xb xc; xc \<in> set (g xb); xc \<in> (if h xb then UNIV else {})\<rbrakk> \<Longrightarrow> False"
    by (metis Cons.prems(2) assms distinct.simps(2) inj2_on_def iso_tuple_UNIV_I)

  then have 4: "distinct (concat (map (\<lambda>y. []) (g x)))"
    using distinct_concat_Nil by auto

  show ?case using 1 2 3 4 by auto
qed

subsection\<open>Specializations of @{term "inj2"}\<close>

subsubsection"Cons"

lemma Cons_inj2: "inj2 (#)"
  unfolding inj2_on_def by simp

lemma Cons_distinct_concat_map: "\<lbrakk>distinct ys; distinct xs\<rbrakk> \<Longrightarrow> distinct [x#y. x \<leftarrow> xs, y \<leftarrow> ys]"
  using inj2_distinct_concat_map Cons_inj2 by auto

lemma Cons_distinct_concat_map_function:
  "\<lbrakk>\<forall> x \<in> set xs. distinct (g x) ; distinct xs\<rbrakk> \<Longrightarrow> distinct [x # y. x \<leftarrow> xs, y \<leftarrow> g x]"
  using inj2_distinct_concat_map_function Cons_inj2 by auto

lemma Cons_distinct_concat_map_function_distinct_on_all:
  "\<lbrakk>\<forall> x. distinct (g x) ; distinct xs\<rbrakk> \<Longrightarrow> distinct [x # y. x \<leftarrow> xs, y \<leftarrow> g x]"
  using Cons_distinct_concat_map_function by (metis (full_types)) 


subsubsection"Node right"

lemma Node_right_inj2: "inj2 (\<lambda>l r. Node l e r)"
  unfolding inj2_on_def by simp

lemma Node_right_distinct_concat_map:
  "\<lbrakk>distinct ys; distinct xs\<rbrakk> \<Longrightarrow> distinct [Node x e y. x \<leftarrow> xs, y \<leftarrow> ys]"
  using inj2_distinct_concat_map Node_right_inj2 by fast


subsubsection"Node left"

lemma Node_left_inj2: "inj2 (\<lambda>r l. Node l e r)"
  unfolding inj2_on_def by simp

lemma Node_left_distinct_map: "distinct xs = distinct (map (\<lambda>l. \<langle>l, (), r\<rangle>) xs)"
  using inj2_distinct_map Node_left_inj2 by fast

subsubsection"Cons Suc"

lemma Cons_Suc_inj2: "inj2 (\<lambda>x ys. Suc x # ys)"
  unfolding inj2_on_def by simp

lemma Cons_Suc_distinct_concat_map_function:
  "\<lbrakk>\<forall> x \<in> set xs. distinct (g x) ; distinct xs\<rbrakk> \<Longrightarrow> distinct [Suc x # y. x \<leftarrow> xs, y \<leftarrow> g x]"
  using inj2_distinct_concat_map_function Cons_Suc_inj2 by auto 


section"Lemmas for cardinality proofs "

lemma length_concat_map: "length [f x r . x \<leftarrow> xs, r \<leftarrow> ys] = length ys * length xs"
  by(induct xs arbitrary: ys) auto

text"An useful extension to \<open>length_concat\<close>"
thm length_concat
lemma length_concat_map_function_sum_list:
  assumes "\<And> x. x \<in> set xs \<Longrightarrow> length (g x) = h x"
  shows "length [f x r . x \<leftarrow> xs, r \<leftarrow> g x] = sum_list (map h xs)"
  using assms by(induct xs) auto

lemma sum_list_extract_last: "(\<Sum>x\<leftarrow>[0..<Suc n]. f x) = (\<Sum>x\<leftarrow>[0..<n]. f x) + f n"
  by(induct n) (auto simp: add.assoc)

lemma leq_sum_to_sum_list: "(\<Sum>x \<le> n. f x) = (\<Sum>x\<leftarrow>[0..<Suc n]. f x)"
  by (metis atMost_upto sum_set_upt_conv_sum_list_nat)

lemma less_sum_to_sum_list: "(\<Sum>x < n. f x) = (\<Sum>x\<leftarrow>[0..< n]. f x)"
  by (simp add: atLeast_upt sum_list_distinct_conv_sum_set)


section"Miscellaneous"

text\<open>Similar to @{thm [source] "length_remove1"}:\<close>
lemma Suc_length_remove1: "x \<in> set xs \<Longrightarrow> Suc (length (remove1 x xs)) = length xs"
  by(induct xs) auto

subsection"\<open>count_list\<close> and replicate"
text"HOL.List doesn't have many lemmas about \<open>count_list\<close> (when not using multisets)"

lemma count_list_replicate: "count_list (replicate x y) y = x" 
  by (induct x) auto
       
lemma count_list_full_elem: "count_list xs y = length xs \<longleftrightarrow> (\<forall>x \<in> set xs. x = y)" 
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons z xs)
  have "\<lbrakk>count_list xs y = Suc (length xs); x \<in> set xs\<rbrakk> \<Longrightarrow> x = y" for x
    by (metis Suc_n_not_le_n count_le_length)
  then show ?case
    using Cons by auto
qed

text\<open>The following lemma verifies the reverse of @{thm [source] "count_notin"}:\<close>
thm count_notin
lemma count_list_zero_not_elem: "count_list xs x = 0 \<longleftrightarrow> x \<notin> set xs" 
  by(induct xs) auto

lemma count_list_length_replicate: "count_list xs y = length xs \<longleftrightarrow> xs = replicate (length xs) y"
  by (metis count_list_full_elem count_list_replicate replicate_length_same)

lemma count_list_True_False: "count_list xs True + count_list xs False = length xs"
  by(induct xs) auto


end