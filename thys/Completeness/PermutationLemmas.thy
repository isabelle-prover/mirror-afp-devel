section "Permutation Lemmas"

theory PermutationLemmas
imports "HOL-Library.Multiset"
begin

  \<comment> \<open>following function is very close to that in multisets- now we can make the connection that x <~~> y iff the multiset of x is the same as that of y\<close>

subsection "perm, count equivalence"

lemma count_eq:
  \<open>count_list xs x = Multiset.count (mset xs) x\<close>
  by (induction xs) simp_all

lemma perm_count: "mset A = mset B \<Longrightarrow> (\<forall> x. count_list A x = count_list B x)"
  by (simp add: count_eq)

lemma count_0: "(\<forall>x. count_list B x = 0) = (B = [])"
  by (simp add: count_list_0_iff)

lemma count_Suc: "count_list B a = Suc m \<Longrightarrow> a \<in> set B"
  by (metis Zero_not_Suc count_notin)

lemma count_perm: "!! B. (\<forall> x. count_list A x = count_list B x) \<Longrightarrow> mset A = mset B"
  by (simp add: count_eq multiset_eq_iff)

lemma perm_count_conv: "mset A = mset B \<longleftrightarrow> (\<forall> x. count_list A x = count_list B x)"
  by (simp add: count_eq multiset_eq_iff)


subsection "Properties closed under Perm and Contr hold for x iff hold for remdups x"

lemma remdups_append: "y \<in> set ys \<Longrightarrow> remdups (ws@y#ys) = remdups (ws@ys)"
  by (induct ws; force)

lemma perm_contr': 
  assumes perm: "\<And>xs ys. mset xs = mset ys \<Longrightarrow> (P xs = P ys)"
  and contr': "\<And>x xs. P(x#x#xs) = P (x#xs)" 
  shows "length xs = n \<Longrightarrow> (P xs = P (remdups xs))"
proof(induction n arbitrary: xs rule: less_induct)
  case (less x)
  show ?case
  proof (cases "distinct xs")
    case True
    then show ?thesis
      by (simp add: distinct_remdups_id)
  next
    case False
    then obtain ws ys zs y where xs: "xs = ws@[y]@ys@[y]@zs"
      using not_distinct_decomp by blast 
    have "P xs = P (ws@[y]@ys@[y]@zs)" by (simp add: xs)
    also have "... = P ([y,y]@ws@ys@zs)" 
      by (intro perm) auto
    also have "... = P ([y]@ws@ys@zs)"
      by (simp add: contr')
    also have "... = P (ws@ys@[y]@zs)" 
      by (intro perm) auto
    also have "... = P (remdups (ws@ys@[y]@zs))"
      using less xs by force
    also have "(remdups (ws@ys@[y]@zs)) = (remdups xs)"
      by (simp add: xs remdups_append) 
    finally show ?thesis .
  qed
qed

lemma perm_contr: 
  assumes perm: "\<And>xs ys. mset xs = mset ys \<Longrightarrow> (P xs = P ys)"
  and contr': "\<And>x xs. P(x#x#xs) = P (x#xs)" 
shows "(P xs = P (remdups xs))"
  using perm_contr'[OF perm contr']
  by presburger


subsection "List properties closed under Perm, Weak and Contr are monotonic in the set of the list"

definition
  rem :: "'a => 'a list => 'a list" where
  "rem x xs = filter (%y. y ~= x) xs"

lemma rem: "x \<notin> set (rem x xs)"
  by(simp add: rem_def)

lemma length_rem: "length (rem x xs) <= length xs"
  by(simp add: rem_def)

lemma rem_notin: "x \<notin> set xs \<Longrightarrow> rem x xs = xs"
  by (metis (mono_tags, lifting) filter_True rem_def)

lemma perm_weak_filter':
  assumes perm: "\<And>xs ys. mset xs = mset ys \<Longrightarrow> (P xs = P ys)"
    and weak: "\<And>x xs. P xs \<Longrightarrow> P (x#xs)"
    and P: "P (ys@filter Q xs)"
  shows "P (ys@xs)"
proof -
  define zs where \<open>zs = filter (Not \<circ> Q) xs\<close>
  have \<open>P (filter Q xs @ ys)\<close>
    by (metis P perm union_code union_commute)
  then have \<open>P (zs @ filter Q xs @ ys)\<close>
    by (induction zs) (simp_all add: weak)
  moreover have "mset (zs @ filter Q xs @ ys) = mset (ys @ xs)"
    by (simp add: zs_def)
  ultimately show \<open>P (ys @ xs)\<close>
    using perm by blast
qed

lemma perm_weak_filter: 
  assumes perm: "\<And>xs ys. mset xs = mset ys \<Longrightarrow> (P xs = P ys)"
    and weak: "\<And>x xs. P xs \<Longrightarrow> P (x#xs)"
  shows "P (filter Q xs) \<Longrightarrow> P xs"
  by (metis append_Nil perm perm_weak_filter' weak)

  \<comment> \<open>Now can prove that in presence of perm, 
  contr and weak, if @{term "set x \<subseteq> set y"} and  @{term "P x"} then @{term "P y"}\<close>

lemma perm_weak_contr_mono: 
  assumes perm: "\<And>xs ys. mset xs = mset ys \<Longrightarrow> (P xs = P ys)"
    and contr: "\<And>x xs. P(x#x#xs) \<Longrightarrow> P (x#xs)" 
    and weak: "\<And>x xs. P xs \<Longrightarrow> P (x#xs)"
    and xy: "set x \<subseteq> set y"
    and Px: "P x"
  shows "P y"
proof -
  from contr weak have contr': "\<And>x xs. P(x#x#xs) = P (x#xs)" by blast
  define y' where "y' \<equiv> filter (\<lambda>z. z \<in> set x) y"
  from xy have "set x = set y'" 
    by (force simp: y'_def)
  hence rxry': "mset (remdups x) = mset (remdups y')"
    using set_eq_iff_mset_remdups_eq by auto 
  from Px perm_contr[OF perm contr'] have Prx: "P (remdups x)"
    by blast
  with rxry' have "P (remdups y')"
    using perm by blast
  with perm_contr[OF perm contr'] have "P y'" by simp
  thus "P y"
    using perm perm_weak_filter weak y'_def by blast 
qed

end
