(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Auxiliary Facts\<close>

theory Preliminaries2
  imports Main "~~/src/HOL/Library/Infinite_Set"
begin

subsection \<open>Finite and Infinite Sets\<close>

lemma finite_product:
  assumes fst: "finite (fst ` A)"
  and     snd: "finite (snd ` A)"
  shows   "finite A"
proof -
  have "A \<subseteq> (fst ` A) \<times> (snd ` A)"
    by force
  thus ?thesis
    using snd fst finite_subset by blast
qed

lemma infinite_Union:
  assumes "infinite(\<Union>A)"
  assumes "finite A"
  obtains M where "M \<in> A" and "infinite M"
  using assms finite_Union by blast

inductive finite_ordered :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> bool" for f :: "'a \<Rightarrow> nat" 
where
  empty_ordered: "finite_ordered f {}"
| insert_ordered: "finite_ordered f A \<Longrightarrow> (\<And>b. b \<in> A \<Longrightarrow> f b \<le> f a) \<Longrightarrow> finite_ordered f (insert a A)"

lemma sort_list:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "sort_key f xs = a @ [z] @ b"
  assumes "y \<in> set a"
  shows "f y \<le> f z"
proof -
  have "sorted ((map f a @ [f z]) @ map f b)"
    using assms(1) sorted_sort_key[of f xs] 
    unfolding map_append by simp
  hence "sorted (map f a @ [f z])"
    using sorted_append by blast
  hence "\<forall>fy \<in> set (map f a). fy \<le> f z"
    unfolding sorted_append by simp
  thus ?thesis
    using `y \<in> set a` set_map by simp
qed

lemma finite_to_finite_ordered:
  "finite A \<Longrightarrow> finite_ordered f A" 
proof -
  assume "finite A"
  then obtain xs where "set xs = A"
    using finite_list by blast
  moreover
  obtain ys where "set xs = set ys" 
    and "\<And>a b y z. ys = a @ [z] @ b \<Longrightarrow> y \<in> set a \<Longrightarrow> f y \<le> f z"
    using sort_list[of f xs] set_sort by metis
  moreover
  have "finite_ordered f (foldl (\<lambda>S x. insert x S) {} ys)"
    using `\<And>a b y z. ys = a @ [z] @ b \<Longrightarrow> y \<in> set a \<Longrightarrow> f y \<le> f z`
  proof (induction ys rule: rev_induct)
    case (snoc y ys)
      hence "finite_ordered f (foldl (\<lambda>S x. insert x S) {} ys)"
        by simp
      moreover
      have "\<And>z. z \<in> set ys \<Longrightarrow> f z \<le> f y"
        using snoc by simp
      moreover
      have "set ys = (foldl (\<lambda>S x. insert x S) {} ys)"
        by (induction ys rule: rev_induct) auto
      ultimately
      show ?case 
        unfolding foldl_append foldl.simps 
        using insert_ordered by metis
  qed (simp add: empty_ordered)
  moreover
  have "set ys = (foldl (\<lambda>S x. insert x S) {} ys)"
    by (induction ys rule: rev_induct) auto
  ultimately
  show ?thesis
    by simp
qed

lemma finite_finite_ordered_eq:
  "finite A = finite_ordered f A"
  by (rule, blast intro: finite_to_finite_ordered, induction rule: finite_ordered.induct, auto)

lemma finite_induct_ordered [case_names empty insert, induct set: finite]:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite S"
  assumes "P {}" 
  assumes "\<And>x S. finite S \<Longrightarrow> (\<And>y. y \<in> S \<Longrightarrow> f y \<le> f x) \<Longrightarrow> P S \<Longrightarrow> P (insert x S)"
  shows "P S"
  using `finite S` unfolding finite_finite_ordered_eq[of _ f] 
proof (induction rule: finite_ordered.induct) 
  case (insert_ordered A a)
    thus ?case
      using assms unfolding finite_finite_ordered_eq[of _ f] by simp
qed (blast intro: `P {}`)

subsection \<open>Cofinite Filters\<close>

lemma almost_all_commutative:
  "finite S \<Longrightarrow> (\<forall>x \<in> S. \<forall>\<^sub>\<infinity>i. P x (i::nat)) = (\<forall>\<^sub>\<infinity>i. \<forall>x \<in> S. P x i)"
proof (induction rule: finite_induct) 
  case (insert x S)
    {
      assume "\<forall>x \<in> insert x S. \<forall>\<^sub>\<infinity>i. P x i"
      hence "\<forall>\<^sub>\<infinity>i. \<forall>x \<in> S. P x i" and "\<forall>\<^sub>\<infinity>i. P x i"
        using insert by simp+
      then obtain i\<^sub>1 i\<^sub>2 where "\<And>j. j \<ge> i\<^sub>1 \<Longrightarrow> \<forall>x \<in> S. P x j"
        and "\<And>j. j \<ge> i\<^sub>2 \<Longrightarrow> P x j"
        unfolding MOST_nat_le by auto
      hence "\<And>j. j \<ge> max i\<^sub>1 i\<^sub>2 \<Longrightarrow> \<forall>x \<in> S \<union> {x}. P x j"
        by simp
      hence "\<forall>\<^sub>\<infinity>i. \<forall>x \<in> insert x S. P x i"
        unfolding MOST_nat_le by blast
    }
    moreover
    have "\<forall>\<^sub>\<infinity>i. \<forall>x \<in> insert x S. P x i \<Longrightarrow> \<forall>x \<in> insert x S. \<forall>\<^sub>\<infinity>i. P x i"
      unfolding MOST_nat_le by auto
    ultimately
    show ?case 
      by blast
qed simp

lemma almost_all_commutative':
  "finite S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> \<forall>\<^sub>\<infinity>i. P x (i::nat)) \<Longrightarrow> (\<forall>\<^sub>\<infinity>i. \<forall>x \<in> S. P x i)"
  using almost_all_commutative by blast

fun index
where
  "index P = (if \<forall>\<^sub>\<infinity>i. P i then Some (LEAST i. \<forall>j \<ge> i. P j) else None)"

lemma index_properties: 
  fixes i :: nat
  shows "index P = Some i \<Longrightarrow> 0 < i \<Longrightarrow> \<not> P (i - 1)"
    and "index P = Some i \<Longrightarrow> j \<ge> i \<Longrightarrow> P j"
proof -
  assume "index P = Some i"
  moreover
  hence i_def: "i = (LEAST i. \<forall>j \<ge> i. P j)" and "\<forall>\<^sub>\<infinity>i. P i"
    unfolding index.simps using option.distinct(2) option.sel 
    by (metis (erased, lifting))+
  then obtain i' where "\<forall>j \<ge> i'.  P j"
    unfolding MOST_nat_le by blast
  ultimately
  show "\<And>j. j \<ge> i \<Longrightarrow> P j"
    using LeastI[of "\<lambda>i. \<forall>j \<ge> i. P j"] by (metis i_def) 
  {
    assume "0 < i"
    then obtain j where "i = Suc j" and "j < i"
      using lessE by blast
    hence "\<And>j'. j' > j \<Longrightarrow> P j'"
      using `\<And>j. j \<ge> i \<Longrightarrow> P j` by force
    hence "\<not> P j"
      using not_less_Least[OF `j < i`[unfolded i_def]] by (metis leI le_antisym)
    thus "\<not> P (i - 1)"
      unfolding `i = Suc j` by simp
  }
qed

end