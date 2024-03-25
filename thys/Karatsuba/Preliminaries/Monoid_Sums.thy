section "Sums in Monoids"

theory Monoid_Sums
  imports "HOL-Algebra.Ring" "Expander_Graphs.Extra_Congruence_Method" Karatsuba_Preliminaries "HOL-Library.Multiset" "HOL-Number_Theory.Residues" Karatsuba_Sum_Lemmas
begin

text "This section contains a version of @{term sum_list} for entries in some abelian monoid.
Contrary to @{term sum_list}, which is defined for the type class @{class comm_monoid_add}, this
version is for the locale @{locale abelian_monoid}.
After the definition, some simple lemmas about sums are proven for this sum function."

context abelian_monoid
begin

fun monoid_sum_list :: "['c \<Rightarrow> 'a, 'c list] \<Rightarrow> 'a" where
  "monoid_sum_list f [] = \<zero>"
| "monoid_sum_list f (x # xs) = f x \<oplus> monoid_sum_list f xs"

lemma "monoid_sum_list f xs = foldr (\<oplus>) (map f xs) \<zero>"
  by (induction xs) simp_all

end

text "The syntactic sugar used for @{const finsum} is adapted accordingly."

(* adapted from finsum syntax definition *)
syntax
  "_monoid_sum_list" :: "index \<Rightarrow> idt \<Rightarrow> 'c list \<Rightarrow> 'c \<Rightarrow> 'a"
      ("(3\<Oplus>__\<leftarrow>_. _)" [1000, 0, 51, 10] 10)
translations
  "\<Oplus>\<^bsub>G\<^esub>i\<leftarrow>xs. b" \<rightleftharpoons> "CONST abelian_monoid.monoid_sum_list G (\<lambda>i. b) xs"

context abelian_monoid
begin

lemma monoid_sum_list_finsum:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier G"
  assumes "distinct xs"
  shows "(\<Oplus>i \<leftarrow> xs. f i) = (\<Oplus>i \<in> set xs. f i)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case using finsum_insert[of "set xs" a f] by simp
qed

lemma monoid_sum_list_cong:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i = g i"
  shows "(\<Oplus>i \<leftarrow> xs. f i) = (\<Oplus>i \<leftarrow> xs. g i)"
  using assms by (induction xs) simp_all

lemma monoid_sum_list_closed[simp]:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> xs. f i) \<in> carrier G"
  using assms by (induction xs) simp_all

lemma monoid_sum_list_add_in:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier G"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> g i \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> xs. f i) \<oplus> (\<Oplus>i \<leftarrow> xs. g i) = 
                    (\<Oplus>i \<leftarrow> xs. f i \<oplus> g i)"
  using assms
proof (induction xs)
  case (Cons a xs)
  have "(\<Oplus>i \<leftarrow> (a # xs). f i) \<oplus> (\<Oplus>i \<leftarrow> (a # xs). g i)
      = (f a \<oplus> (\<Oplus>i \<leftarrow> xs. f i)) \<oplus> (g a \<oplus> (\<Oplus>i \<leftarrow> xs. g i))"
    by simp
  also have "... = (f a \<oplus> g a) \<oplus> ((\<Oplus>i \<leftarrow> xs. f i) \<oplus> (\<Oplus>i \<leftarrow> xs. g i))"
    using a_comm a_assoc Cons.prems by simp
  also have "... = (f a \<oplus> g a) \<oplus> (\<Oplus>i \<leftarrow> xs. f i \<oplus> g i)"
    using Cons by simp
  finally show ?case by simp
qed simp

lemma monoid_sum_list_0[simp]: "(\<Oplus>i \<leftarrow> xs. \<zero>) = \<zero>"
  by (induction xs) simp_all

lemma monoid_sum_list_swap:
  assumes[simp]: "\<And>i j. i \<in> set xs \<Longrightarrow> j \<in> set ys \<Longrightarrow> f i j \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> xs. (\<Oplus>j \<leftarrow> ys. f i j)) = 
                 (\<Oplus>j \<leftarrow> ys. (\<Oplus>i \<leftarrow> xs. f i j))"
  using assms
proof (induction xs arbitrary: ys)
  case (Cons a xs)
  have "(\<Oplus>i \<leftarrow> (a # xs). (\<Oplus>j \<leftarrow> ys. f i j))
      = (\<Oplus>j \<leftarrow> ys. f a j) \<oplus> (\<Oplus>i \<leftarrow> xs. (\<Oplus>j \<leftarrow> ys. f i j))"
    by simp
  also have "... = (\<Oplus>j \<leftarrow> ys. f a j) \<oplus> (\<Oplus>j \<leftarrow> ys. (\<Oplus>i \<leftarrow> xs. f i j))"
    using Cons by simp
  also have "... = (\<Oplus>j \<leftarrow> ys. f a j \<oplus> (\<Oplus>i \<leftarrow> xs. f i j))"
    using monoid_sum_list_add_in[of ys "\<lambda>j. f a j" "\<lambda>j. (\<Oplus>i \<leftarrow> xs. f i j)"] Cons.prems by simp
  finally show ?case by simp
qed simp

lemma monoid_sum_list_index_transformation:
  "(\<Oplus>i \<leftarrow> (map g xs). f i) = (\<Oplus>i \<leftarrow> xs. f (g i))"
  by (induction xs) simp_all

lemma monoid_sum_list_index_shift_0:
  "(\<Oplus>i \<leftarrow> [c..<c+n]. f i) = (\<Oplus>i \<leftarrow> [0..<n]. f (c + i))"
  using monoid_sum_list_index_transformation[of f "\<lambda>i. c + i" "[0..<n]"]
  by (simp add: add.commute map_add_upt)

lemma monoid_sum_list_index_shift:
  "(\<Oplus>l \<leftarrow> [a..<b]. f (l+c)) = (\<Oplus>l \<leftarrow> [(a+c)..<(b+c)]. f l)"
  using monoid_sum_list_index_transformation[of f "\<lambda>i. i + c" "[a..<b]"]
  by (simp add: map_add_const_upt)

lemma monoid_sum_list_app:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier G"
  assumes "\<And>i. i \<in> set ys \<Longrightarrow> f i \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> xs @ ys. f i) = (\<Oplus>i \<leftarrow> xs. f i) \<oplus> (\<Oplus>i \<leftarrow> ys. f i)"
  using assms
  by (induction xs) (simp_all add: a_assoc)

lemma monoid_sum_list_app':
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier G"
  assumes "\<And>i. i \<in> set ys \<Longrightarrow> f i \<in> carrier G"
  assumes "xs @ ys = zs"
  shows "(\<Oplus>i \<leftarrow> zs. f i) = (\<Oplus>i \<leftarrow> xs. f i) \<oplus> (\<Oplus>i \<leftarrow> ys. f i)"
  using monoid_sum_list_app assms by blast

lemma monoid_sum_list_extract:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier G"
  assumes "\<And>i. i \<in> set ys \<Longrightarrow> f i \<in> carrier G"
  assumes "f x \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> xs @ x # ys. f i) = f x \<oplus> (\<Oplus>i \<leftarrow> (xs @ ys). f i)"
proof -
  have "(\<Oplus>i \<leftarrow> xs @ x # ys. f i) = (\<Oplus>i \<leftarrow> xs. f i) \<oplus> f x \<oplus> (\<Oplus>i \<leftarrow> ys. f i)"
    using assms monoid_sum_list_app[of xs f "x # ys"]
    using a_assoc by auto
  also have "... = f x \<oplus> ((\<Oplus>i \<leftarrow> xs. f i) \<oplus> (\<Oplus>i \<leftarrow> ys. f i))"
    using assms a_assoc a_comm by auto
  finally show ?thesis using monoid_sum_list_app[of xs f ys] assms by algebra
qed

lemma monoid_sum_list_Suc:
  assumes "\<And>i. i < Suc r \<Longrightarrow> f i \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> [0..<Suc r]. f i) = (\<Oplus>i \<leftarrow> [0..<r]. f i) \<oplus> f r"
  using assms monoid_sum_list_app[of "[0..<r]" f "[r]"]
  by simp

lemma bij_betw_diff_singleton: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> bij_betw f A B \<Longrightarrow> f a = b \<Longrightarrow> bij_betw f (A - {a}) (B - {b})"
  by (metis (no_types, lifting) DiffE Diff_Diff_Int Diff_cancel Diff_empty Int_insert_right_if1 Un_Diff_Int notIn_Un_bij_betw3 singleton_iff)

lemma "a \<in> A \<Longrightarrow> bij_betw f A B \<Longrightarrow> bij_betw f (A - {a}) (B - {f a})"
  using bij_betw_diff_singleton[of a A "f a" B f]
  by (simp add: bij_betwE)  

lemma monoid_sum_list_multiset_eq:
  assumes "mset xs = mset ys"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> xs. f i) = (\<Oplus>i \<leftarrow> ys. f i)"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have "a \<in> set ys" using mset_eq_setD by fastforce
  then obtain ys1 ys2 where "ys = ys1 @ a # ys2" by (meson split_list)
  with Cons.prems have 1: "mset xs = mset (ys1 @ ys2)" by simp
  from Cons.prems mset_eq_setD have "\<And>i. i \<in> set ys \<Longrightarrow> f i \<in> carrier G" by blast
  then have[simp]: "\<And>i. i \<in> set ys1 \<Longrightarrow> f i \<in> carrier G" "f a \<in> carrier G" "\<And>i. i \<in> set ys2 \<Longrightarrow> f i \<in> carrier G"
    using \<open>ys = ys1 @ a # ys2\<close> by simp_all
  from 1 have "(\<Oplus>i \<leftarrow> xs. f i) = (\<Oplus>i \<leftarrow> (ys1 @ ys2). f i)"
    using Cons by simp
  also have "... = (\<Oplus>i \<leftarrow> ys1. f i) \<oplus> (\<Oplus>i \<leftarrow> ys2. f i)"
    by (intro monoid_sum_list_app) simp_all
  also have "f a \<oplus> ... = (\<Oplus>i \<leftarrow> ys1. f i) \<oplus> (f a \<oplus> (\<Oplus>i \<leftarrow> ys2. f i))"
    using a_comm a_assoc monoid_sum_list_closed by simp
  also have "... = (\<Oplus>i \<leftarrow> ys1. f i) \<oplus> (\<Oplus>i \<leftarrow> (a # ys2). f i)"
    by simp
  also have "... = (\<Oplus>i \<leftarrow> ys. f i)"
    unfolding \<open>ys = ys1 @ a # ys2\<close>
    by (intro monoid_sum_list_app[symmetric]) auto
  finally show ?case by simp
qed
lemma monoid_sum_list_index_permutation:
  assumes "distinct xs"
  assumes "distinct ys \<or> length xs = length ys"
  assumes "bij_betw f (set xs) (set ys)"
  assumes "\<And>i. i \<in> set ys \<Longrightarrow> g i \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> ys. g i) = (\<Oplus>i \<leftarrow> xs. g (f i))"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then have "ys = []" using bij_betw_same_card by fastforce
  then show ?case by simp
next
  case (Cons a xs)
  then have "length ys = length (a # xs)" "distinct ys"
    by (metis bij_betw_same_card distinct_card, metis bij_betw_same_card distinct_card card_distinct)
  
  have 0: "\<And>i. i \<in> set (a # xs) \<Longrightarrow> g (f i) \<in> carrier G"
  proof -
    fix i
    assume "i \<in> set (a # xs)"
    then have "f i \<in> set ys" using Cons.prems(3) by (simp add: bij_betw_apply)
    then show "g (f i) \<in> carrier G" using Cons.prems(4) by blast
  qed
  
  define b where "b = f a"
  then have "b \<in> set ys" using Cons(4) bij_betw_apply by fastforce
  then obtain ys1 ys2 where "ys = ys1 @ b # ys2" by (meson split_list)
  then have "b \<notin> set ys1" "b \<notin> set ys2" using \<open>distinct ys\<close> by simp_all
  have "bij_betw f (set xs) (set (ys1 @ ys2))"
    using \<open>ys = ys1 @ b # ys2\<close> Cons(4) b_def
    using bij_betw_diff_singleton[of a "set (a # xs)" "f a" "set ys" f]
    using Cons.prems(1) \<open>distinct ys\<close> by auto
  moreover have "length (ys1 @ ys2) = length xs" using \<open>length ys = length (a # xs)\<close> \<open>ys = ys1 @ b # ys2\<close>
    by simp
  ultimately have 1: "(\<Oplus>i \<leftarrow> (ys1@ys2). g i) = (\<Oplus>i \<leftarrow> xs. g (f i))" using Cons.IH[of "ys1@ys2"] Cons.prems(4)
    using Cons.prems(1) 0 \<open>ys = ys1 @ b # ys2\<close> by auto

  have "(\<Oplus>i \<leftarrow> (a # xs). g (f i)) = g b \<oplus> (\<Oplus>i \<leftarrow> xs. g (f i))"
    using \<open>b = f a\<close> by simp
  also have "... = g b \<oplus> (\<Oplus>i \<leftarrow> (ys1@ys2). g i)" using 1 by simp
  also have "... = (\<Oplus>i \<leftarrow> (ys1@b#ys2). g i)"
    apply (intro monoid_sum_list_extract[symmetric])
    using Cons.prems(4) \<open>ys = ys1 @ b # ys2\<close> by simp_all
  finally show "(\<Oplus>i \<leftarrow> ys. g i) = (\<Oplus>i \<leftarrow> (a # xs). g (f i))"
    using \<open>ys = ys1 @ b # ys2\<close> by simp
qed

lemma monoid_sum_list_split:
  assumes[simp]: "\<And>i. i < b + c \<Longrightarrow> f i \<in> carrier G"
  shows "(\<Oplus>l \<leftarrow> [0..<b]. f l) \<oplus> (\<Oplus>l \<leftarrow> [b..< b + c]. f l) = (\<Oplus>l \<leftarrow> [0..< b + c]. f l)" 
  using monoid_sum_list_app[of "[0..<b]" f "[b..< b + c]", symmetric]
  using upt_add_eq_append[of 0 b c]
  by simp

lemma monoid_sum_list_splice:
  assumes[simp]: "\<And>i. i < 2 * n \<Longrightarrow> f i \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> [0..< 2 * n]. f i) = (\<Oplus>i \<leftarrow> [0..<n]. f (2*i)) \<oplus> (\<Oplus>i \<leftarrow> [0..<n]. f (2*i+1))"
proof -
  let ?es = "filter even [0..< 2 * n]"
  let ?os = "filter odd [0..< 2 * n]"
  have 1: "(\<Oplus>i \<leftarrow> [0..< 2 * n]. f i) = (\<Oplus>i \<in> {0..< 2 * n}. f i)"
    using monoid_sum_list_finsum[of "[0..< 2 * n]" f] by simp

  let ?E = "{i \<in> {0..<2*n}. even i}"
  let ?O = "{i \<in> {0..<2*n}. odd i}"
  have "?E \<inter> ?O = {}" by blast
  moreover have "?E \<union> ?O = {0..<2*n}" by blast
  ultimately have "(\<Oplus>i \<in> {0..<2*n}. f i) = (\<Oplus>i \<in> ?E. f i) \<oplus> (\<Oplus>i \<in> ?O. f i)"
    using finsum_Un_disjoint[of ?E ?O f] assms by auto
  moreover have "?E = set ?es" "?O = set ?os" by simp_all
  ultimately have "(\<Oplus>i \<in> {0..<2*n}. f i) = (\<Oplus>i \<in> set ?es. f i) \<oplus> (\<Oplus>i \<in> set ?os. f i)"
    by presburger
  also have "(\<Oplus>i \<in> set ?es. f i) = (\<Oplus>i \<leftarrow> ?es. f i)"
    using monoid_sum_list_finsum[of ?es f] by simp
  also have "... = (\<Oplus>i \<leftarrow> [0..<n]. f (2*i))"
    using monoid_sum_list_index_transformation[of f "\<lambda>i. 2 * i" "[0..<n]"]
    using filter_even_upt_even
    by algebra
  also have "(\<Oplus>i \<in> set ?os. f i) = (\<Oplus>i \<leftarrow> ?os. f i)"
    using monoid_sum_list_finsum[of ?os f] by simp
  also have "... = (\<Oplus>i \<leftarrow> [0..<n]. f (2*i + 1))"
    using monoid_sum_list_index_transformation[of f "\<lambda>i. 2 * i + 1" "[0..<n]"]
    using filter_odd_upt_even
    by algebra
  finally show ?thesis using 1 by presburger
qed

lemma monoid_sum_list_even_odd_split:
  assumes "even (n::nat)"
  assumes "\<And>i. i < n \<Longrightarrow> f i \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> [0..<n]. f i) = (\<Oplus>i \<leftarrow> [0..< n div 2]. f (2*i)) \<oplus> (\<Oplus>i \<leftarrow> [0..< n div 2]. f (2*i+1))"
  using assms monoid_sum_list_splice by auto

end

context abelian_group
begin

lemma monoid_sum_list_minus_in:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier G"
  shows "\<ominus> (\<Oplus>i \<leftarrow> xs. f i) = (\<Oplus>i \<leftarrow> xs. \<ominus> f i)"
  using assms by (induction xs) (simp_all add: minus_add)

lemma monoid_sum_list_diff_in:
  assumes[simp]: "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier G"
  assumes[simp]: "\<And>i. i \<in> set xs \<Longrightarrow> g i \<in> carrier G"
  shows "(\<Oplus>i \<leftarrow> xs. f i) \<ominus> (\<Oplus>i \<leftarrow> xs. g i) = 
                    (\<Oplus>i \<leftarrow> xs. f i \<ominus> g i)"
proof -
  have "(\<Oplus>i \<leftarrow> xs. f i) \<ominus> (\<Oplus>i \<leftarrow> xs. g i) = (\<Oplus>i \<leftarrow> xs. f i) \<oplus> (\<ominus> (\<Oplus>i \<leftarrow> xs. g i))"
    unfolding minus_eq by simp
  also have "... = (\<Oplus>i \<leftarrow> xs. f i) \<oplus> (\<Oplus>i \<leftarrow> xs. \<ominus> g i)"
    using monoid_sum_list_minus_in[of xs g] by simp
  also have "... = (\<Oplus>i \<leftarrow> xs. f i \<oplus> (\<ominus> g i))"
    using monoid_sum_list_add_in[of xs f] by simp
  finally show ?thesis unfolding minus_eq .
qed

end

context ring
begin

lemma monoid_sum_list_const:
  assumes[simp]: "c \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> xs. c) = (nat_embedding (length xs)) \<otimes> c"
  apply (induction xs)
  using a_comm l_distr by auto

lemma monoid_sum_list_in_right:
  assumes "y \<in> carrier R"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> xs. f i \<otimes> y) = (\<Oplus>i \<leftarrow> xs. f i) \<otimes> y"
  using assms by (induction xs) (simp_all add: l_distr)

lemma monoid_sum_list_in_left:
  assumes "y \<in> carrier R"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> xs. y \<otimes> f i) = y \<otimes> (\<Oplus>i \<leftarrow> xs. f i)"
  using assms by (induction xs) (simp_all add: r_distr)

lemma monoid_sum_list_prod:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier R"
  assumes "\<And>i. i \<in> set ys \<Longrightarrow> g i \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> xs. f i) \<otimes> (\<Oplus>j \<leftarrow> ys. g j) = (\<Oplus>i \<leftarrow> xs. (\<Oplus>j \<leftarrow> ys. f i \<otimes> g j))"
proof -
  have "(\<Oplus>i \<leftarrow> xs. f i) \<otimes> (\<Oplus>j \<leftarrow> ys. g j) = (\<Oplus>i \<leftarrow> xs. f i \<otimes> (\<Oplus>j \<leftarrow> ys. g j))"
    apply (intro monoid_sum_list_in_right[symmetric])
    using assms by simp_all
  also have "... = (\<Oplus>i \<leftarrow> xs. (\<Oplus>j \<leftarrow> ys. f i \<otimes> g j))"
    apply (intro monoid_sum_list_cong monoid_sum_list_in_left[symmetric])
    using assms by simp_all
  finally show ?thesis .
qed

subsection \<open>Kronecker delta\<close>

definition delta where
"delta i j = (if i = j then \<one> else \<zero>)"

lemma delta_closed[simp]: "delta i j \<in> carrier R"
  unfolding delta_def by simp

lemma delta_sym: "delta i j = delta j i"
  unfolding delta_def by simp

lemma delta_refl[simp]: "delta i i = \<one>"
  unfolding delta_def by simp

lemma monoid_sum_list_delta[simp]:
  assumes[simp]: "\<And>i. i < n \<Longrightarrow> f i \<in> carrier R"
  assumes[simp]: "j < n"
  shows "(\<Oplus>i \<leftarrow> [0..<n]. delta i j \<otimes> f i) = f j"
proof -
  from assms have 0: "[0..<n] = [0..<j] @ j # [Suc j..<n]"
    by (metis le_add1 le_add_same_cancel1 less_imp_add_positive upt_add_eq_append upt_conv_Cons)
  then have "[0..<n] = [0..<j] @ [j] @ [Suc j..<n]"
    by simp
  moreover have 1: "\<And>i. i \<in> set [0..<j] \<Longrightarrow> delta i j \<otimes> f i \<in> carrier R"
    using 0 assms delta_closed m_closed atLeastLessThan_iff
    by (metis le_add1 less_imp_add_positive linorder_le_less_linear set_upt upt_conv_Nil)
  moreover have 2: "\<And>i. i \<in> set ([j] @ [Suc j..<n]) \<Longrightarrow> delta i j \<otimes> f i \<in> carrier R"
    using 0 assms delta_closed m_closed
    by auto
  ultimately have "(\<Oplus>i \<leftarrow> [0..<n]. delta i j \<otimes> f i) = (\<Oplus>i \<leftarrow> [0..<j]. delta i j \<otimes> f i) \<oplus> (\<Oplus>i \<leftarrow> [j] @ [Suc j..<n]. delta i j \<otimes> f i)"
    using monoid_sum_list_app[of "[0..<j]" "\<lambda>i. delta i j \<otimes> f i" "[j] @ [Suc j..<n]"]
    by presburger
  also have "(\<Oplus>i \<leftarrow> [j] @ [Suc j..<n]. delta i j \<otimes> f i) = (\<Oplus>i \<leftarrow> [j]. delta i j \<otimes> f i) \<oplus> (\<Oplus>i \<leftarrow> [Suc j..<n]. delta i j \<otimes> f i)"
    using 2 monoid_sum_list_app[of "[j]" "\<lambda>i. delta i j \<otimes> f i" "[Suc j..<n]"]
    by simp
  also have "(\<Oplus>i \<leftarrow> [0..<j]. delta i j \<otimes> f i) = \<zero>"
    using monoid_sum_list_0[of "[0..<j]"] monoid_sum_list_cong[of "[0..<j]" "\<lambda>i. \<zero>" "\<lambda>i. delta i j \<otimes> f i"]
    unfolding delta_def using \<open>j < n\<close> by simp
  also have "(\<Oplus>i \<leftarrow> [Suc j..<n]. delta i j \<otimes> f i) = \<zero>"
    using monoid_sum_list_0[of "[Suc j..<n]"] monoid_sum_list_cong[of "[Suc j..<n]" "\<lambda>i. \<zero>" "\<lambda>i. delta i j \<otimes> f i"]
    unfolding delta_def by simp
  also have "(\<Oplus>i \<leftarrow> [j]. delta i j \<otimes> f i) = f j" by simp
  finally show ?thesis by simp
qed

lemma mononid_sum_list_only_delta[simp]:
  "j < n \<Longrightarrow> (\<Oplus>i \<leftarrow> [0..<n]. delta i j) = \<one>"
  using monoid_sum_list_delta[of n "\<lambda>i. \<one>" j] by simp

subsection \<open>Power sums\<close>

lemma geo_monoid_list_sum: 
  assumes[simp]: "x \<in> carrier R"
  shows "(\<one> \<ominus> x) \<otimes> (\<Oplus>l \<leftarrow> [0..<r]. x [^] l) = (\<one> \<ominus> x [^] r)"
  using assms
proof (induction r)
  case 0
  then show ?case using assms by (simp, algebra)
next
  case (Suc r)
  have "(\<one> \<ominus> x) \<otimes> (\<Oplus>l \<leftarrow> [(0::nat)..< Suc r]. x [^] l) = (\<one> \<ominus> x) \<otimes> (x [^] r \<oplus> (\<Oplus>l \<leftarrow> [0..<r]. x [^] l))"
    using monoid_sum_list_Suc[of r "\<lambda>l. x [^] l"] a_comm
    by simp

  also have "... = (\<one> \<ominus> x) \<otimes> x [^] r \<oplus> (\<one> \<ominus> x) \<otimes> (\<Oplus>l \<leftarrow> [0..<r]. x [^] l)"
    using r_distr by auto
  also have "... = x [^] r \<ominus> x [^] (Suc r) \<oplus> (\<one> \<ominus> x) \<otimes> (\<Oplus>l \<leftarrow> [0..<r]. x [^] l)"
    apply (intro arg_cong2[where f = "(\<oplus>)"] refl)
    unfolding minus_eq
     l_distr[OF one_closed a_inv_closed[OF \<open>x \<in> carrier R\<close>] nat_pow_closed[OF \<open>x \<in> carrier R\<close>]]
    using \<open>x \<in> carrier R\<close>
    using l_minus nat_pow_Suc2 by force
  also have "... = x [^] r \<ominus> x [^] (Suc r) \<oplus> (\<one> \<ominus> x [^] r)"
    using Suc by presburger
  also have "... = \<one> \<ominus> x [^] (Suc r)"
    using one_closed minus_add assms nat_pow_closed[of x] by algebra
  finally show ?case .
qed

text "rewrite @{thm nat_pow_pow} and @{thm mult.commute} inside power sum"
lemma monoid_pow_sum_nat_pow_pow:
  assumes "x \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] ((g i :: nat) * h i)) = (\<Oplus>i \<leftarrow> xs. f i \<otimes> (x [^] h i) [^] g i)"
  apply (intro_cong "[cong_tag_2 (\<otimes>)]" more: monoid_sum_list_cong refl)
  using nat_pow_pow[OF assms] by (simp add: mult.commute)

end

context cring
begin

text "Split a power sum at some term"
lemma monoid_pow_sum_list_split:
  assumes "l + k = n"
  assumes "\<And>i. i < n \<Longrightarrow> f i \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> x [^] i) =
    (\<Oplus>i \<leftarrow> [0..<l]. f i \<otimes> x [^] i) \<oplus>
    x [^] l \<otimes> (\<Oplus>i \<leftarrow> [0..<k]. f (l + i) \<otimes> x [^] i)"
proof -
  have "(\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> x [^] i) =
    (\<Oplus>i \<leftarrow> [0..<l]. f i \<otimes> x [^] i) \<oplus>
    (\<Oplus>i \<leftarrow> [l..<n]. f i \<otimes> x [^] i)"
    apply (intro monoid_sum_list_app' m_closed nat_pow_closed upt_add_eq_append'[symmetric])
    using assms by simp_all
  also have "(\<Oplus>i \<leftarrow> [l..<n]. f i \<otimes> x [^] i) =
    (\<Oplus>i \<leftarrow> [0..<k]. f (l + i) \<otimes> x [^] (l + i))"
    using monoid_sum_list_index_shift_0[of _ l "n-l"] \<open>l + k = n\<close>
    by fastforce
  also have "... = (\<Oplus>i \<leftarrow> [0..<k]. x [^] l \<otimes> (f (l + i) \<otimes> x [^] i))"
    apply (intro monoid_sum_list_cong)
    using assms m_comm m_assoc nat_pow_mult[symmetric, OF \<open>x \<in> carrier R\<close>] by simp
  also have "... = x [^] l \<otimes> (\<Oplus>i \<leftarrow> [0..<k]. f (l + i) \<otimes> x [^] i)"
    apply (intro monoid_sum_list_in_left m_closed nat_pow_closed)
    using assms by simp_all
  finally show ?thesis .
qed

text "split power sum at term, more general"
lemma monoid_pow_sum_split:
  assumes "l + k = n"
  assumes "\<And>i. i < n \<Longrightarrow> f i \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> x [^] (i * c)) =
    (\<Oplus>i \<leftarrow> [0..<l]. f i \<otimes> x [^] (i * c)) \<oplus>
    x [^] (l * c) \<otimes> (\<Oplus>i \<leftarrow> [0..<k]. f (l + i) \<otimes> x [^] (i * c))"
proof -
  have "(\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> x [^] (i * c)) = (\<Oplus>i \<leftarrow> [0..<n]. f i \<otimes> (x [^] c) [^] i)"
    by (intro monoid_pow_sum_nat_pow_pow \<open>x \<in> carrier R\<close>)
  also have "... = (\<Oplus>i \<leftarrow> [0..<l]. f i \<otimes> (x [^] c) [^] i) \<oplus>
    (x [^] c) [^] l \<otimes> (\<Oplus>i \<leftarrow> [0..<k]. f (l + i) \<otimes> (x [^] c) [^] i)"
    by (intro monoid_pow_sum_list_split assms nat_pow_closed) argo
  also have "... = (\<Oplus>i \<leftarrow> [0..<l]. f i \<otimes> x [^] (i * c)) \<oplus>
    x [^] (c * l) \<otimes> (\<Oplus>i \<leftarrow> [0..<k]. f (l + i) \<otimes> x [^] (i * c))"
    by (intro_cong "[cong_tag_2 (\<oplus>), cong_tag_2 (\<otimes>)]" more: monoid_pow_sum_nat_pow_pow[symmetric] nat_pow_pow \<open>x \<in> carrier R\<close>)
  also have "... = (\<Oplus>i \<leftarrow> [0..<l]. f i \<otimes> x [^] (i * c)) \<oplus>
    x [^] (l * c) \<otimes> (\<Oplus>i \<leftarrow> [0..<k]. f (l + i) \<otimes> x [^] (i * c))"
    by (intro_cong "[cong_tag_2 (\<oplus>), cong_tag_2 (\<otimes>), cong_tag_2 ([^])]" more: refl mult.commute)
  finally show ?thesis .
qed 

subsubsection "Algebraic operations"

text "addition"
lemma monoid_pow_sum_add:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier R"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> g i \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] (i::nat)) \<oplus> (\<Oplus>i \<leftarrow> xs. g i \<otimes> x [^] i) = (\<Oplus>i \<leftarrow> xs. (f i \<oplus> g i) \<otimes> x [^] i)"
proof -
  have "(\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] i) \<oplus> (\<Oplus>i \<leftarrow> xs. g i \<otimes> x [^] i) =
    (\<Oplus>i \<leftarrow> xs. (f i \<otimes> x [^] i) \<oplus> (g i \<otimes> x [^] i))"
    apply (intro monoid_sum_list_add_in m_closed nat_pow_closed assms) by assumption+
  also have "... = (\<Oplus>i \<leftarrow> xs. (f i \<oplus> g i) \<otimes> x [^] i)"
    apply (intro monoid_sum_list_cong l_distr[symmetric] nat_pow_closed assms) by assumption+
  finally show ?thesis .
qed

lemma monoid_pow_sum_add':
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier R"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> g i \<in> carrier R"
  assumes "x \<in> carrier R"
shows "(\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] ((i::nat) * c)) \<oplus> (\<Oplus>i \<leftarrow> xs. g i \<otimes> x [^] (i * c)) = (\<Oplus>i \<leftarrow> xs. (f i \<oplus> g i) \<otimes> x [^] (i * c))"
proof -
  have "(\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] ((i::nat) * c)) \<oplus> (\<Oplus>i \<leftarrow> xs. g i \<otimes> x [^] (i * c)) =
    (\<Oplus>i \<leftarrow> xs. (f i \<otimes> (x [^] c) [^] i)) \<oplus> (\<Oplus>i \<leftarrow> xs. (g i \<otimes> (x [^] c) [^] i))"
    by (intro_cong "[cong_tag_2 (\<oplus>)]" more: monoid_pow_sum_nat_pow_pow \<open>x \<in> carrier R\<close>)
  also have "... = (\<Oplus>i \<leftarrow> xs. (f i \<oplus> g i) \<otimes> (x [^] c) [^] i)"
    apply (intro monoid_pow_sum_add nat_pow_closed) using assms by simp_all
  also have "... = (\<Oplus>i \<leftarrow> xs. (f i \<oplus> g i) \<otimes> x [^] (i * c))"
    by (intro monoid_pow_sum_nat_pow_pow[symmetric] \<open>x \<in> carrier R\<close>)
  finally show ?thesis .
qed

text "unary minus"
lemma monoid_pow_sum_minus:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "\<ominus> (\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] (i :: nat)) = (\<Oplus>i \<leftarrow> xs. (\<ominus> f i) \<otimes> x [^] i)"
proof -
  have "\<ominus> (\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] (i :: nat)) = (\<Oplus>i \<leftarrow> xs. \<ominus> (f i \<otimes> x [^] (i :: nat)))"
    apply (intro monoid_sum_list_minus_in m_closed nat_pow_closed assms) by assumption
  also have "... = (\<Oplus>i \<leftarrow> xs. (\<ominus> f i) \<otimes> x [^] i)"
    apply (intro monoid_sum_list_cong l_minus[symmetric] nat_pow_closed assms) by assumption
  finally show ?thesis .
qed

text "minus"
lemma monoid_pow_sum_diff:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier R"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> g i \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] (i::nat)) \<ominus> (\<Oplus>i \<leftarrow> xs. g i \<otimes> x [^] (i :: nat)) =
      (\<Oplus>i \<leftarrow> xs. (f i \<ominus> g i) \<otimes> x [^] i)"
  using assms
  by (simp add: minus_eq monoid_pow_sum_add[symmetric] monoid_pow_sum_minus)

lemma monoid_pow_sum_diff':
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> f i \<in> carrier R"
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> g i \<in> carrier R"
  assumes "x \<in> carrier R"
  shows "(\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] ((i::nat) * c)) \<ominus> (\<Oplus>i \<leftarrow> xs. g i \<otimes> x [^] (i * c)) =
      (\<Oplus>i \<leftarrow> xs. (f i \<ominus> g i) \<otimes> x [^] (i * c))"
proof -
  have "(\<Oplus>i \<leftarrow> xs. f i \<otimes> x [^] ((i::nat) * c)) \<ominus> (\<Oplus>i \<leftarrow> xs. g i \<otimes> x [^] (i * c)) =
    (\<Oplus>i \<leftarrow> xs. f i \<otimes> (x [^] c) [^] i) \<ominus> (\<Oplus>i \<leftarrow> xs. g i \<otimes> (x [^] c) [^] i)"
    by (intro_cong "[cong_tag_2 (\<lambda>i j. i \<ominus> j)]" more: monoid_pow_sum_nat_pow_pow \<open>x \<in> carrier R\<close>)
  also have "... = (\<Oplus>i \<leftarrow> xs. (f i \<ominus> g i) \<otimes> (x [^] c) [^] i)"
    apply (intro monoid_pow_sum_diff nat_pow_closed) using assms by simp_all
  also have "... = (\<Oplus>i \<leftarrow> xs. (f i \<ominus> g i) \<otimes> x [^] (i * c))"
    by (intro monoid_pow_sum_nat_pow_pow[symmetric] \<open>x \<in> carrier R\<close>)
  finally show ?thesis .
qed

end

subsection "@{term monoid_sum_list} in the context @{locale residues}"

context residues
begin

lemma monoid_sum_list_eq_sum_list:
"(\<Oplus>\<^bsub>R\<^esub> i \<leftarrow> xs. f i) = (\<Sum>i \<leftarrow> xs. f i) mod m"
  apply (induction xs)
  subgoal by (simp add: zero_cong)
  subgoal for a xs by (simp add: mod_add_right_eq res_add_eq)
  done

lemma monoid_sum_list_mod_in:
"(\<Oplus>\<^bsub>R\<^esub> i \<leftarrow> xs. f i) = (\<Oplus>\<^bsub>R\<^esub> i \<leftarrow> xs. (f i) mod m)"
  by (induction xs) (simp_all add: mod_add_left_eq res_add_eq)

lemma monoid_sum_list_eq_sum_list':
"(\<Oplus>\<^bsub>R\<^esub> i \<leftarrow> xs. f i mod m) = (\<Sum>i \<leftarrow> xs. f i) mod m"
  using monoid_sum_list_eq_sum_list monoid_sum_list_mod_in by metis

end

end