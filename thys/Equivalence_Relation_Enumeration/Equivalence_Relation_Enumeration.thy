section \<open>Introduction\<close>

theory Equivalence_Relation_Enumeration
  imports "HOL-Library.Sublist" "HOL-Library.Disjoint_Sets"
    "Card_Equiv_Relations.Card_Equiv_Relations"
begin

text \<open>As mentioned in the abstract the enumeration algorithm relies on the bijection between
restricted growth functions (RGFs) of length @{term "n"} and the equivalence relations on
@{term "{..<n}"}, where the bijection is the operation that forms the equivalence kernels of an RGF.
The method is being dicussed, for example, by~\<^cite>\<open>"hutchinson1963" and "milne1977"\<close> or
\<^cite>\<open>\<open>\textsection 1.5\<close> in "white1986"\<close>.

An enumeration algorithm for RGFs is less convoluted than one for equivalence relations or
partitions and the representation has the advantage that checking whether a pair of elements are
equivalent can be done by performing two list lookup operations.

After a few preliminary results in the following section, Section~\ref{sec:enum_rgf} introduces the
enumeration algorithm for RGFs and shows that the function enumerates all of them (for the given
length) without repetition. Section~\ref{sec:bij_kernel} shows that the operation of forming the 
equivalence kernel is a bijection and concludes with the correctness of the entire algorithm. In
Section~\ref{sec:app} an interesting application is being discussed, where the enumeration of
partitions is applied within a proof. Section~\ref{sec:add} contains a few additional results,
such as the fact that the length of the enumerated list is a Bell number. The latter result relies
on the formalization of the cardinality of equivalence relations by
Bulwahn~\<^cite>\<open>"Card_Equiv_Relations-AFP"\<close>.\<close>

section \<open>Preliminary Results\<close>

text \<open>This section contains a few preliminary results used in the proofs below.\<close>

lemma length_filter:"length (filter p xs) = sum_list (map (\<lambda>x. of_bool ( p x)) xs)"
  by (induct xs, simp_all)

lemma count_list_expand:"count_list xs x = length (filter ((=) x) xs)"
  by (induct xs, simp_all)

text \<open>An induction schema (similar to @{thm [source] list_induct2} and @{thm [source] rev_induct}) 
for two lists of equal length, where induction step is shown appending elements at the end.\<close>

lemma list_induct_2_rev[consumes 1, case_names Nil Cons]:
  assumes "length x = length y"
  assumes "P [] []"
  assumes "\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs@[x]) (ys@[y])"
  shows "P x y"
  using assms(1)
proof (induct "length x" arbitrary: x y)
  case 0
  then show ?case using assms(2) by simp
next
  case (Suc n)
  obtain x1 x2 where a:"x = x1@[x2]" and c:"length x1 = n"
    by (metis Suc(2) append_butlast_last_id length_append_singleton 
        length_greater_0_conv nat.inject zero_less_Suc)

  obtain y1 y2 where b:"y = y1@[y2]" and d:"length y1 = n"
    by (metis Suc(2,3) append_butlast_last_id length_append_singleton 
        length_greater_0_conv nat.inject zero_less_Suc)

  have "P x1 y1" using c d Suc by simp
  hence "P (x1@[x2]) (y1@[y2])" using assms(3) c d by simp
  thus ?case using a b by simp
qed

text \<open>If all but one value of a sum is zero then it can be evaluated on the remaining point:\<close>

lemma sum_collapse: 
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add}"
  assumes "finite A"
  assumes "z \<in> A"
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<noteq> z \<Longrightarrow> f y = 0"
  shows "sum f A = f z"
  using sum.union_disjoint[where A="A-{z}" and B="{z}" and g="f"]
  by (simp add: assms sum.insert_if)

text \<open>Number of occurrences of elements in lists is preserved under injective maps.\<close>

lemma count_list_inj_map:
  assumes "inj_on f (set x)"
  assumes "y \<in> set x"
  shows "count_list (map f x) (f y) = count_list x y"
  using assms by (induction x, simp_all, fastforce)

text \<open>A relation cannot be an equivalence relation on two distinct sets.\<close>

lemma equiv_on_unique:
  assumes "equiv A p"
  assumes "equiv B p"
  shows "A = B"
  by (meson assms equalityI equiv_class_eq_iff subsetI)

text \<open>The restriction of an equivalence relation is itself an equivalence relation.\<close>

lemma equiv_subset:
  assumes "B \<subseteq> A"
  assumes "equiv A p"
  shows "equiv B (Restr p B)"
proof -
  have "refl_on B (Restr p B)" using assms by (simp add:refl_on_def equiv_def, blast)
  moreover have "sym (Restr p B)" using assms by (simp add:sym_def equiv_def)
  moreover have "trans (Restr p B)"
    using assms by (simp add:trans_def equiv_def, blast)
  ultimately show ?thesis by (simp add:equiv_def)
qed

section \<open>Enumerating Restricted Growth Functions\label{sec:enum_rgf}\<close>

fun rgf_limit :: "nat list \<Rightarrow> nat"
  where 
    "rgf_limit [] = 0" |
    "rgf_limit (x#xs) = max (x+1) (rgf_limit xs)"

lemma rgf_limit_snoc: "rgf_limit (x@[y]) = max (y+1) (rgf_limit x)"
  by (induction x, simp_all)

lemma rgf_limit_ge: "y \<in> set xs \<Longrightarrow> y < rgf_limit xs"
  by (induction xs, simp_all, metis lessI max_less_iff_conj not_less_eq)

definition rgf :: "nat list \<Rightarrow> bool"
  where "rgf x = (\<forall>ys y. prefix (ys@[y]) x \<longrightarrow> y \<le> rgf_limit ys)"

text \<open>The function @{term "rgf_limit"} returns the smallest natural number larger than all list
elements, it is the largest allowed value following @{term "xs"} for restricted growth functions.
The definition @{term "rgf"} is the predicate capturing the notion.\<close>

fun enum_rgfs :: "nat \<Rightarrow> (nat list) list"
  where
    "enum_rgfs 0 = [[]]" |
    "enum_rgfs (Suc n) = [(x@[y]). x \<leftarrow> enum_rgfs n,  y \<leftarrow> [0..<rgf_limit x+1]]"

text \<open>The function @{term "enum_rgfs n"} returns all RGFs of length @{term "n"} without repetition.
The fact is verified in the three lemmas at the end of this section.\<close>

lemma rgf_snoc:
  "rgf (xs@[x]) \<longleftrightarrow> rgf xs \<and> x < rgf_limit xs + 1"
  unfolding rgf_def by (rule order_antisym, (simp add:less_Suc_eq_le)+)

lemma rgf_imp_initial_segment:
  "rgf xs \<Longrightarrow> set xs = {..<rgf_limit xs}"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  have c:"rgf xs" using snoc(2) rgf_snoc by simp 
  hence a:"set xs = {..<rgf_limit xs}" using snoc(1) by simp
  have b: "x \<le> rgf_limit xs" using snoc(2) rgf_snoc c by simp
  have "set (xs@[x]) = insert x {..<rgf_limit xs}"
    using a by simp
  also have "... = {..<max (x+1) (rgf_limit xs)}" using b
    by (cases "x < rgf_limit xs", simp add:insert_absorb, simp add:lessThan_Suc)
  also have "... = {..<rgf_limit (xs@[x])}"
    using rgf_limit_snoc by simp
  finally show ?case by simp
qed

lemma enum_rgfs_returns_rgfs:
  assumes "x \<in> set (enum_rgfs n)"
  shows "rgf x"
  using assms
proof (induction n arbitrary: x)
  case 0
  then show ?case by (simp add:rgf_def)
next
  case (Suc n)
  obtain x1 x2 where 
    x_def:"x = x1@[x2]" "x2 < rgf_limit x1 + 1" "x1 \<in> set (enum_rgfs n)"
    using Suc by (simp add:image_iff, force) 
  have a:"rgf x1" using Suc x_def by blast
  thus ?case using x_def by (simp add:rgf_snoc)
qed

lemma enum_rgfs_len:
  assumes "x \<in> set (enum_rgfs n)"
  shows "length x = n"
  using assms by (induction n arbitrary: x, simp_all, fastforce) 

lemma equiv_rels_enum:
  assumes "rgf x"
  shows "count_list (enum_rgfs (length x)) x = 1"
  using assms
proof (induction x rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  have b:"rgf xs" using snoc(2) rgf_def by simp 
  hence "x < rgf_limit xs + 1" using rgf_snoc snoc by blast
  hence a:"card ({0..<rgf_limit xs + 1} \<inter> {x}) = 1" by force
  have "1 = count_list (enum_rgfs (length xs)) xs" using snoc b by simp
  also have "... = (\<Sum>r1\<leftarrow>enum_rgfs (length xs). of_bool (xs = r1) * 
      card ({0..<rgf_limit xs + 1} \<inter> {x}))"
    using a by (simp add:length_concat filter_concat count_list_expand length_filter)
  also have "... = (\<Sum>r1\<leftarrow>enum_rgfs (length xs). of_bool (xs = r1) * 
      card ({0..<rgf_limit r1 + 1} \<inter> {x}))"
    by (metis (mono_tags, opaque_lifting) mult_eq_0_iff of_bool_eq_0_iff)
  also have "... = (\<Sum>r1\<leftarrow>enum_rgfs (length xs). of_bool (xs = r1) * 
      (\<Sum>r2\<leftarrow>[0..<rgf_limit r1 + 1]. of_bool (x = r2)))"
    by (simp add:interv_sum_list_conv_sum_set_nat del:One_nat_def)
  also have "... = length (filter ((=) (xs@[x])) (enum_rgfs (length (xs@[x]))))"
    by (simp add:length_concat filter_concat length_filter comp_def 
        of_bool_conj sum_list_const_mult del:upt_Suc)
  also have "... = count_list (enum_rgfs (length (xs@[x]))) (xs@[x])"
    by (simp add:count_list_expand length_filter del:enum_rgfs.simps)
  finally show ?case by presburger
qed

section \<open>Enumerating Equivalence Relations\label{sec:bij_kernel}\<close>

text \<open>The following definition returns the equivalence relation induced by a list, for example, by
a restricted growth function.\<close>

definition kernel_of :: "'a list \<Rightarrow> nat rel"
  where "kernel_of xs = {(i,j). i < length xs \<and> j < length xs \<and> xs ! i = xs ! j}"

text \<open>Using that the enumeration function for equivalence relations on @{term "{..<n}"} is
straight-forward to define:\<close>

definition equiv_rels where "equiv_rels n = map kernel_of (enum_rgfs n)"

text \<open>The following lemma shows that the image of 
@{term "kernel_of"} is indeed an equivalence relation:\<close>

lemma kernel_of_equiv: "equiv {..<length xs} (kernel_of xs)"
proof -
  have "kernel_of xs \<subseteq> {..<length xs} \<times> {..<length xs}"
    by (rule subsetI, simp add:kernel_of_def mem_Times_iff case_prod_beta)
  thus ?thesis by (simp add:equiv_def refl_on_def sym_def trans_def kernel_of_def)
qed

lemma kernel_of_eq_len:
  assumes "kernel_of x = kernel_of y"
  shows "length x = length y"
proof -
  have "{..<length x} = {..<length y}"
    by (metis kernel_of_equiv equiv_on_unique assms)
  thus ?thesis by simp
qed

lemma kernel_of_eq:
  "(kernel_of x = kernel_of y) \<longleftrightarrow> 
  (length x = length y \<and> (\<forall>j < length x. \<forall>i < j. (x ! i = x ! j) = (y ! i = y ! j)))"
proof (cases "length x = length y")
  case True
  have "(kernel_of x = kernel_of y)  \<longleftrightarrow>
    (\<forall>j < length x. \<forall>i < length x. (x ! i = x ! j) = (y ! i = y ! j))"
    unfolding set_eq_iff kernel_of_def using True by (simp, blast)
  also have "... \<longleftrightarrow> (\<forall>j < length x. \<forall>i < j. (x ! i = x ! j) = (y ! i = y ! j))"
    by (metis (no_types, lifting) linorder_cases order.strict_trans)
  finally show ?thesis using True by simp
next
  case False
  then show ?thesis using kernel_of_eq_len by blast
qed

lemma kernel_of_snoc:
  "kernel_of (xs) = Restr (kernel_of (xs@[x]))  {..<length xs}"
  by (simp add:kernel_of_def nth_append set_eq_iff) 

lemma kernel_of_inj_on_rgfs_aux:
  assumes "length x = length y"
  assumes "rgf x"
  assumes "rgf y"
  assumes "kernel_of x = kernel_of y"
  shows "x = y"
  using assms
proof (induct x y rule: list_induct_2_rev)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  have a:"kernel_of xs = kernel_of ys" 
    using Cons(1,5) kernel_of_snoc by metis
  have d:"rgf xs" "rgf ys" using Cons rgf_def by auto
  hence b:"xs = ys" using Cons(2) a by auto
  have "\<And>i. i < length xs \<Longrightarrow> (xs ! i = x) = (ys ! i = y)"
  proof -
    fix i
    assume i_l:"i < length xs"
    have "(xs ! i = x) \<longleftrightarrow> (i,length xs) \<in> kernel_of (xs@[x])" using i_l
      by (simp add:kernel_of_def less_Suc_eq nth_append) 
    also have "... \<longleftrightarrow> (i,length xs) \<in> kernel_of (ys@[y])"
      using Cons(5) by simp
    also have "... \<longleftrightarrow> (ys ! i= y)" using  i_l Cons(1)
      by (simp add:kernel_of_def less_Suc_eq nth_append) 
    finally show "(xs ! i = x) = (ys ! i = y)" by simp
  qed
  hence c:"(x \<in> set xs \<longrightarrow> x = y) \<and> (x \<notin> set xs \<longrightarrow> y \<notin> set ys)"
    by (metis b in_set_conv_nth)
  have x_bound:"x < rgf_limit xs + 1"
    using Cons(3) rgf_snoc d by simp
  have y_bound:"y < rgf_limit ys + 1"
    using Cons(4) rgf_snoc d by simp
  have "x = y" using b c d rgf_imp_initial_segment Cons x_bound y_bound
    apply (cases "x < rgf_limit xs", simp)
    by (cases "y < rgf_limit ys", simp+)
  then show ?case using b by simp
qed

lemma kernel_of_inj_on_rgfs:
  "inj_on kernel_of {x. rgf x}"
  by (rule inj_onI, simp, metis kernel_of_eq_len kernel_of_inj_on_rgfs_aux) 

text \<open>Applying an injective map to a list preserves the induced relation:\<close>

lemma kernel_of_under_inj_map:
  assumes "inj_on f (set x)"
  shows "kernel_of x = kernel_of (map f x)"
proof -
  have "\<And>i j. i < length x \<Longrightarrow> j < length x 
    \<Longrightarrow> (map f x) ! i = (map f x) ! j \<Longrightarrow> x ! i = x ! j"
    using assms by (simp add: inj_on_eq_iff)
  thus ?thesis unfolding kernel_of_def by fastforce
qed

lemma all_rels_are_kernels:
  assumes "equiv {..<n} p"
  shows "\<exists>(x :: nat set list). kernel_of x = p \<and> length x = n"
proof -
  define r where "r = map (\<lambda>k. p``{k}) [0..<n]"

  have "\<And> u v. (u,v) \<in> kernel_of r \<longleftrightarrow> (u,v) \<in> p"
  proof -
    fix u v :: nat
    have "(u,v) \<in> kernel_of r \<longleftrightarrow> ((u,v) \<in> {..<n}\<times>{..<n} \<and> p``{u} = p``{v})"
      unfolding kernel_of_def r_def by auto
    also have "... \<longleftrightarrow> (u,v) \<in> p" by (metis assms equiv_class_eq_iff mem_Sigma_iff)
    finally show "(u,v) \<in> kernel_of r \<longleftrightarrow> (u,v) \<in> p" by simp
  qed
  hence "kernel_of r = p" by auto
  moreover have "length r = n" using r_def by simp
  ultimately show ?thesis by auto
qed

text \<open>For any list there is always an injective map on its set, such that its image is an RGF.\<close>

lemma map_list_to_rgf:
  "\<exists>f. inj_on f (set x) \<and> rgf (map f x)"
proof (induction "length x" arbitrary: x)
  case 0
  then show ?case by (simp add:rgf_def)
next
  case (Suc n)
  obtain x1 x2 where x_def: "x = x1@[x2]" and l_x1: "length x1 = n"
    by (metis append_butlast_last_id length_append_singleton Suc(2) 
        length_greater_0_conv nat.inject zero_less_Suc)
  obtain f where inj_f: "inj_on f (set x1)" and pc_f: "rgf (map f x1)"
    using Suc(1) l_x1 by blast
  show ?case
  proof (cases "x2 \<in> set x1")
    case True
    have a:"set x = set x1" using x_def True by auto
    hence b:"inj_on f (set x)" using inj_f by auto

    have "f x2 < rgf_limit (map f x1)" using rgf_limit_ge True by auto
    hence "rgf (map f x)" 
      by (simp add:x_def rgf_snoc pc_f)
    then show ?thesis using b by blast
  next
    case False
    define f' where "f' = (\<lambda>y. if y \<in> set x1 then f y else rgf_limit (map f x1))"
    have "inj_on f' (set x1)" using f'_def inj_f by (simp add: inj_on_def)
    moreover have "rgf_limit (map f x1) \<notin> set (map f x1)"
      using rgf_limit_ge by blast
    hence "f' x2 \<notin> f' ` set x1" using False by (simp add:f'_def)
    ultimately have "inj_on f' (insert x2 (set x1))" using False by simp
    hence a:"inj_on f' (set x)" using False x_def by simp

    have b:"map f x1 = map f' x1" using f'_def by simp

    have c:"f' x2 < Suc (rgf_limit (map f x1))" by (simp add:f'_def False)
    have "rgf (map f' x)" by (simp add:x_def b[symmetric] rgf_snoc pc_f c)
    then show ?thesis using a by blast 
  qed
qed

text \<open>For any relation there is a corresponding RGF:\<close>

lemma rgf_exists:
  assumes "equiv {..<n} r"
  shows "\<exists>x. rgf x \<and> length x = n \<and> kernel_of x = r"
proof -
  obtain y :: "nat set list" where a:"kernel_of y = r" "length y = n"
    using all_rels_are_kernels assms by blast
  then obtain f where b:"inj_on f (set y)" "rgf (map f y)"
    using map_list_to_rgf by blast
  have "kernel_of (map f y) = r"
    using kernel_of_under_inj_map a b by blast
  moreover have "length (map f y) = n" using a by simp
  ultimately show ?thesis
    using b by blast
qed

text \<open>These are the main result of this entry: The function @{term "equiv_rels n"} enumerates the
equivalence relations on @{term "{..<n}"} without repetition.\<close>

theorem equiv_rels_set:
  assumes "x \<in> set (equiv_rels n)"
  shows "equiv {..<n} x"
  using assms equiv_rels_def kernel_of_equiv enum_rgfs_len by auto

theorem equiv_rels:
  assumes "equiv {..<n} r"
  shows "count_list (equiv_rels n) r = 1"
proof -
  obtain y where y_def: "rgf y" "length y = n" "kernel_of y = r"
    using rgf_exists assms by blast

  have a: "\<And>x. x \<in> set (enum_rgfs n) \<Longrightarrow> (kernel_of y = kernel_of x) = (y=x)"
    using enum_rgfs_returns_rgfs y_def(1,2) enum_rgfs_len inj_onD[OF kernel_of_inj_on_rgfs]
    by auto

  have "count_list (equiv_rels n) r = 
    length (filter (\<lambda>x. r = kernel_of x) (enum_rgfs n))"
    by (simp add:equiv_rels_def count_list_expand length_filter comp_def)
  also have "... = length (filter (\<lambda>x. kernel_of y = kernel_of x) (enum_rgfs n))"
    using y_def(3) by simp
  also have "... = length (filter (\<lambda>x. y = x) (enum_rgfs n))"
    using a by (simp cong:filter_cong)
  also have "... = count_list (enum_rgfs n) y"
    by (simp add:count_list_expand length_filter)
  also have "... = 1"
    using equiv_rels_enum y_def(1,2) by auto
  finally show ?thesis by simp
qed

text \<open>A corollary of the previous theorem is that the sum of the indicator function for a relation
over @{term "equiv_rels n"} is always one.\<close>

corollary equiv_rels_2:
  assumes "n = length xs"
  shows "(\<Sum>x\<leftarrow>equiv_rels n. of_bool (kernel_of xs = x)) = (1 :: 'a :: {semiring_1})"
proof -
  have "length (filter (\<lambda>x. kernel_of xs = x) (equiv_rels (length xs))) = 1"
    using equiv_rels[OF kernel_of_equiv[where xs="xs"]] assms by (simp add:count_list_expand)
  thus ?thesis
    using assms by (simp add:of_bool_def sum_list_map_filter'[symmetric] sum_list_triv)
qed

section \<open>Example Application\label{sec:app}\<close>

text \<open>In this section, I wanted to discuss an interesting application within the context of
a proof in Isabelle. This is motivated by a real-world example \<^cite>\<open>\<open>\textsection 2.2\<close> in "alon1999"\<close>,
where a function in a 4-times iterated sum could only be reduced by splitting it according to the
equivalence relation formed by the indices. The notepad below illustrates how this can be done
(in the case of 3 index variables).\<close>

notepad
begin \<^marker>\<open>tag visible\<close>
  fix f :: "nat \<times> nat \<times> nat  \<Rightarrow> nat"
  fix I :: "nat set"
  assume a:"finite I"

  text \<open>To be able to break down such a sum by partitions let us introduce the function $P$
    which is defined to be sum of an indicator function over all possible equivalence relations
    its argument can form:\<close>

  define P :: "nat list \<Rightarrow> nat"
    where "P = (\<lambda>xs. (\<Sum>x \<leftarrow> equiv_rels (length xs). of_bool (kernel_of xs = x) ))"

  text \<open>Note that its value is always one, hence we can introduce it in an algebraic equation easily:\<close> 

  have P_one: "\<And>xs. P xs = 1"
    by (simp add: P_def equiv_rels_2)

  note unfold_equiv_rels = P_def equiv_rels_def numeral_eq_Suc kernel_of_eq 
    neq_commute All_less_Suc comp_def

  define r where "r = (\<Sum>i \<in> I. (\<Sum>j \<in> I. (\<Sum>k \<in> I.  f (i,j,k))))"

  text \<open>As a first step, we just introduce the factor @{term "P [i,j,k]"}.\<close>

  have "r = (\<Sum>i \<in> I. (\<Sum>j \<in> I. (\<Sum>k \<in> I.  f (i,j,k) * P [i,j,k])))"
    by (simp add:P_one r_def cong:sum.cong)

  text \<open>By expanding the definition of P and distributing, the sum can be expanded into 5 sums
    each representing a distinct equivalence relation formed by the indices.\<close>

  also have "... =
    (\<Sum>i\<in>I. f (i, i, i)) +
    (\<Sum>i\<in>I. \<Sum>j\<in>I. f (i, i, j) * of_bool (i \<noteq> j)) +
    (\<Sum>i\<in>I. \<Sum>j\<in>I. f (i, j, i) * of_bool (i \<noteq> j)) +
    (\<Sum>i\<in>I. \<Sum>j\<in>I. f (i, j, j) * of_bool (i \<noteq> j)) +
    (\<Sum>i\<in>I. \<Sum>j\<in>I. \<Sum>k\<in>I. f (i, j, k) * of_bool (j \<noteq> k \<and> i \<noteq> k \<and> i \<noteq> j))"
    (is "_ = ?rhs")
    by (simp add:unfold_equiv_rels sum.distrib distrib_left sum_collapse[OF a])
  finally have "r = ?rhs" by simp
end

section \<open>Additional Results\label{sec:add}\<close>

text \<open>If two lists induce the same equivalence relation, then there is a bijection between the sets
that preserves the multiplicities of its elements.\<close>

lemma kernel_of_eq_imp_bij:
  assumes "kernel_of x = kernel_of y"
  shows "\<exists>f. bij_betw f (set x) (set y) \<and> 
    (\<forall>z \<in> set x. count_list x z = count_list y (f z))"
proof -
  obtain x' where x'_def: "inj_on x' (set x)" "rgf (map x' x)"
    using map_list_to_rgf by blast
  obtain y' where y'_def: "inj_on y' (set y)" "rgf (map y' y)"
    using map_list_to_rgf by blast

  have "kernel_of (map x' x) = kernel_of (map y' y)" 
    using assms x'_def(1) y'_def(1)
    by (simp add: kernel_of_under_inj_map[symmetric])
  hence b:"map x' x = map y' y"  
    using inj_onD[OF kernel_of_inj_on_rgfs] x'_def(2) y'_def(2) length_map by simp
  hence f: "x' ` set x = y' ` set y" 
    by (metis list.set_map)
  define f where "f = the_inv_into (set y) y' \<circ> x'"
  have g:"\<And>z. z \<in> set x \<Longrightarrow> count_list x z = count_list y (f z)"
  proof -
    fix z
    assume a:"z \<in> set x"
    have e: "x' z \<in> y' ` set y"
      by (metis a b imageI image_set)
    have c: "the_inv_into (set y) y' (x' z) \<in> set y"
      using e the_inv_into_into[OF y'_def(1)] by simp
    have d: "(y' (the_inv_into (set y) y' (x' z))) = x' z"
      using e f_the_inv_into_f y'_def(1) by force

    have "count_list x z = count_list (map x' x) (x' z)"
      using a x'_def by (simp add: count_list_inj_map)
    also have "... = count_list (map y' y) (x' z)"
      by (simp add:b)
    also have "... = count_list (map y' y) (y' (the_inv_into (set y) y' (x' z)))"
      by (simp add:d)
    also have "... = count_list y (the_inv_into (set y) y' (x' z))"
      using c count_list_inj_map[OF y'_def(1)] by simp
    also have "... = count_list y (f z)" by (simp add:f_def)
    finally show "count_list x z = count_list y (f z)" by simp
  qed

  have "bij_betw x' (set x) (x' ` set x)"
    using x'_def(1) bij_betw_imageI by auto
  moreover have "bij_betw (the_inv_into (set y) y') (y' ` set y) (set y)"
    using bij_betw_the_inv_into[OF bij_betw_imageI] y'_def(1) by auto
  hence "bij_betw (the_inv_into (set y) y') (x' ` set x) (set y)"
    using f by simp
  ultimately have "bij_betw f (set x) (set y)"
    using bij_betw_trans f_def by blast
  thus ?thesis using g by blast
qed

text \<open>As expected the length of @{term "equiv_rels n"} is the $n$-th Bell number.\<close>

lemma len_equiv_rels: "length (equiv_rels n) = Bell n"
proof -
  have a:"finite {p. equiv {..<n} p}" 
    by (simp add: finite_equiv)
  have b: "set (equiv_rels n)  \<subseteq>  {p. equiv {..<n} p}"
    using equiv_rels_set by blast
  have "length (equiv_rels n) = 
    (\<Sum>x \<in> {p. equiv {..<n} p}. count_list (equiv_rels n) x)"
    using a b by (simp add:sum_count_set)
  also have "... = card {p. equiv {..<n} p}"
    by (simp add: equiv_rels)
  also have "... = Bell (card {..<n})"
    using card_equiv_rel_eq_Bell by blast
  also have "... = Bell n" by simp
  finally show ?thesis by simp
qed

text \<open>Instead of forming an equivalence relation from a list, it is also possible to induce a
partition from it:\<close>

definition induced_par :: "'a list \<Rightarrow> nat set set"  where 
  "induced_par xs = (\<lambda>k. {i. i < length xs \<and> xs ! i = k}) ` (set xs)"

text \<open>The following lemma verifies the commutative diagram, i.e.,
@{term "induced_par xs"} is the same partition as the quotient of @{term "{..<length xs}"} over
the corresponding equivalence relation.\<close>

lemma quotient_of_kernel_is_induced_par:
  "{..<length xs} // (kernel_of xs) = (induced_par xs)"
proof (rule set_eqI) 
  fix x
  have "x \<in> {..<length xs} // (kernel_of xs) \<longleftrightarrow> 
    (\<exists>i < length xs. x = {j. j < length xs \<and> xs ! i = xs ! j})"
    unfolding quotient_def kernel_of_def by blast
  also have "... \<longleftrightarrow> (\<exists>y \<in> set xs. x = {j. j < length xs \<and> y = xs ! j})"
    unfolding in_set_conv_nth Bex_def by (rule order_antisym, force+)
  also have "... \<longleftrightarrow> (x \<in> induced_par xs)"
    unfolding induced_par_def by auto
  finally show "x \<in> {..<length xs} // (kernel_of xs) \<longleftrightarrow> (x \<in> induced_par xs)"
    by simp
qed

end
