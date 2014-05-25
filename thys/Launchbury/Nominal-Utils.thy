theory "Nominal-Utils"
imports "../Nominal2/Nominal2" "~~/src/HOL/Library/AList"
begin

subsubsection {* Lemmas helping with equivariance proofs *}

lemma perm_rel_lemma:
  assumes "\<And> \<pi> x y. r (\<pi> \<bullet> x) (\<pi> \<bullet> y) \<Longrightarrow> r x y"
  shows "r (\<pi> \<bullet> x) (\<pi> \<bullet> y) \<longleftrightarrow> r x y" (is "?l \<longleftrightarrow> ?r")
by (metis (full_types) assms permute_minus_cancel(2))

lemma perm_rel_lemma2:
  assumes "\<And> \<pi> x y. r x y \<Longrightarrow> r (\<pi> \<bullet> x) (\<pi> \<bullet> y)"
  shows "r x y \<longleftrightarrow> r (\<pi> \<bullet> x) (\<pi> \<bullet> y)" (is "?l \<longleftrightarrow> ?r")
by (metis (full_types) assms permute_minus_cancel(2))


lemma eqvt_at_apply:
  assumes "eqvt_at f x"
  shows "(p \<bullet> f) x = f x"
by (metis (hide_lams, no_types) assms eqvt_at_def permute_fun_def permute_minus_cancel(1))

lemma eqvt_at_apply':
  assumes "eqvt_at f x"
  shows "p \<bullet> f x = f (p \<bullet> x)"
by (metis (hide_lams, no_types) assms eqvt_at_def)

subsubsection {* Freshness via equivariance *}

lemma eqvt_fresh_cong1: "(\<And>p x. p \<bullet> (f x) = f (p \<bullet> x)) \<Longrightarrow> a \<sharp> x \<Longrightarrow> a \<sharp> f x "
  apply (rule fresh_fun_eqvt_app[of f])
  apply (rule eqvtI)
  apply (rule eq_reflection)
  apply (rule ext)
  apply (metis permute_fun_def permute_minus_cancel(1))
  apply assumption
  done

lemma eqvt_fresh_cong2:
  assumes eqvt: "(\<And>p x y. p \<bullet> (f x y) = f (p \<bullet> x) (p \<bullet> y))"
  and fresh1: "a \<sharp> x" and fresh2: "a \<sharp> y"
  shows "a \<sharp> f x y"
proof-
  have "eqvt (\<lambda> (x,y). f x y)"
    using eqvt
    apply -
    apply (auto simp add: eqvt_def)
    apply (rule ext)
    apply auto
    by (metis permute_minus_cancel(1))
  moreover
  have "a \<sharp> (x, y)" using fresh1 fresh2 by auto
  ultimately
  have "a \<sharp> (\<lambda> (x,y). f x y) (x, y)" by (rule fresh_fun_eqvt_app)
  thus ?thesis by simp
qed

lemma eqvt_fresh_star_cong1:
  assumes eqvt: "(\<And>p x. p \<bullet> (f x) = f (p \<bullet> x))"
  and fresh1: "a \<sharp>* x"
  shows "a \<sharp>* f x"
  by (metis fresh_star_def eqvt_fresh_cong1 assms)

lemma eqvt_fresh_star_cong2:
  assumes eqvt: "(\<And>p x y. p \<bullet> (f x y) = f (p \<bullet> x) (p \<bullet> y))"
  and fresh1: "a \<sharp>* x" and fresh2: "a \<sharp>* y"
  shows "a \<sharp>* f x y"
  by (metis fresh_star_def eqvt_fresh_cong2 assms)

lemma eqvt_fresh_cong3:
  assumes eqvt: "(\<And>p x y z. p \<bullet> (f x y z) = f (p \<bullet> x) (p \<bullet> y) (p \<bullet> z))"
  and fresh1: "a \<sharp> x" and fresh2: "a \<sharp> y" and fresh3: "a \<sharp> z"
  shows "a \<sharp> f x y z"
proof-
  have "eqvt (\<lambda> (x,y,z). f x y z)"
    using eqvt
    apply -
    apply (auto simp add: eqvt_def)
    apply (rule ext)
    apply auto
    by (metis permute_minus_cancel(1))
  moreover
  have "a \<sharp> (x, y, z)" using fresh1 fresh2 fresh3 by auto
  ultimately
  have "a \<sharp> (\<lambda> (x,y,z). f x y z) (x, y, z)" by (rule fresh_fun_eqvt_app)
  thus ?thesis by simp
qed

lemma eqvt_fresh_star_cong3:
  assumes eqvt: "(\<And>p x y z. p \<bullet> (f x y z) = f (p \<bullet> x) (p \<bullet> y) (p \<bullet> z))"
  and fresh1: "a \<sharp>* x" and fresh2: "a \<sharp>* y" and fresh3: "a \<sharp>* z"
  shows "a \<sharp>* f x y z"
  by (metis fresh_star_def eqvt_fresh_cong3 assms)

subsubsection {* Additional simplification rules *}

lemma not_self_fresh[simp]: "atom x \<sharp> x \<longleftrightarrow> False"
  by (metis fresh_at_base(2))

lemma fresh_star_singleton: "{ x } \<sharp>* e \<longleftrightarrow> x \<sharp> e"
  by (simp add: fresh_star_def)

subsubsection {* Additional equivariance lemmas *}

lemma range_eqvt: "\<pi> \<bullet> range Y = range (\<pi> \<bullet> Y)"
  unfolding image_eqvt UNIV_eqvt ..

lemma case_option_eqvt[eqvt]:
  "\<pi> \<bullet> case_option d f x = case_option (\<pi> \<bullet> d) (\<pi> \<bullet> f) (\<pi> \<bullet> x)"
  by(cases x)(simp_all)

lemma funpow_eqvt[simp,eqvt]:
  "\<pi> \<bullet> ((f :: 'a \<Rightarrow> 'a::pt) ^^ n) = (\<pi> \<bullet> f) ^^ (\<pi> \<bullet> n)"
 apply (induct n)
 apply simp
 apply (rule ext)
 apply simp
 apply perm_simp
 apply simp
 done

lemma delete_eqvt[eqvt]:
  "\<pi> \<bullet> AList.delete x \<Gamma> = AList.delete (\<pi> \<bullet> x) (\<pi> \<bullet> \<Gamma>)"
by (induct \<Gamma>, auto)

lemma dom_perm:
  "dom (\<pi> \<bullet> f) = \<pi> \<bullet> (dom f)"
  unfolding dom_def by (perm_simp) (simp)

lemmas dom_perm_rev[simp,eqvt] = dom_perm[symmetric]

lemma ran_perm[simp]:
  "\<pi> \<bullet> (ran f) = ran (\<pi> \<bullet> f)"
  unfolding ran_def by (perm_simp) (simp)

lemma map_add_eqvt[eqvt]:
  "\<pi> \<bullet> (m1 ++ m2) = (\<pi> \<bullet> m1) ++ (\<pi> \<bullet> m2)"
  unfolding map_add_def
  by (perm_simp, rule)

lemma map_of_eqvt[eqvt]:
  "\<pi> \<bullet> map_of l = map_of (\<pi> \<bullet> l)"
  apply (induct l)
  apply (simp add: permute_fun_def)
  apply simp
  apply perm_simp
  apply auto
  done

subsubsection {* Freshness lemmas *}

lemma fresh_list_elem:
  assumes "a \<sharp> \<Gamma>"
  and "e \<in> set \<Gamma>"
  shows "a \<sharp> e"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma set_not_fresh:
  "x \<in> set L \<Longrightarrow> \<not>(atom x \<sharp> L)"
  by (metis fresh_list_elem not_self_fresh)

lemma pure_fresh_star[simp]: "a \<sharp>* (x :: 'a :: pure)"
  by (simp add: fresh_star_def pure_fresh)

lemma supp_set_mem: "x \<in> set L \<Longrightarrow> supp x \<subseteq> supp L"
  by (induct L) (auto simp add: supp_Cons)

lemma set_supp_mono: "set L \<subseteq> set L2 \<Longrightarrow> supp L \<subseteq> supp L2"
  by (induct L)(auto simp add: supp_Cons supp_Nil dest:supp_set_mem)

subsubsection {* Freshness and support for subsets of variables *}

lemma supp_mono: "finite (B::'a::fs set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> supp A \<subseteq> supp B"
  by (metis infinite_super subset_Un_eq supp_of_finite_union)

lemma fresh_subset:
  "finite B \<Longrightarrow> x \<sharp> (B :: 'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<sharp> A"
  by (auto dest:supp_mono simp add: fresh_def)

lemma fresh_star_subset:
  "finite B \<Longrightarrow> x \<sharp>* (B :: 'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<sharp>* A"
  by (metis fresh_star_def fresh_subset)

lemma fresh_star_set_subset:
  "x \<sharp>* (B :: 'a::at_base list) \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> x \<sharp>* A"
  by (metis fresh_star_set fresh_star_subset[OF finite_set])

subsubsection {* The set of free variables of an expression *}

definition fv :: "'a::pt \<Rightarrow> 'b::at_base set" where "fv e = {v. atom v \<in> supp e}"

lemma fv_eqvt[simp,eqvt]: "\<pi> \<bullet> (fv e) = fv (\<pi> \<bullet> e)"
  unfolding fv_def by simp

lemma fv_Nil[simp]: "fv [] = {}"
  by (auto simp add: fv_def supp_Nil)
lemma fv_Cons[simp]: "fv (x # xs) = fv x \<union> fv xs"
  by (auto simp add: fv_def supp_Cons)
lemma fv_Pair[simp]: "fv (x, y) = fv x \<union> fv y"
  by (auto simp add: fv_def supp_Pair)
lemma fv_append[simp]: "fv (x @ y) = fv x \<union> fv y"
  by (auto simp add: fv_def supp_append)
lemma fv_at_base[simp]: "fv a = {a::'a::at_base}"
  by (auto simp add: fv_def supp_at_base)
lemma fv_pure[simp]: "fv (a::'a::pure) = {}"
  by (auto simp add: fv_def pure_supp)

subsubsection {* Other useful lemmas *}

lemma pure_permute_id: "permute p = (\<lambda> x. (x::'a::pure))"
  by rule (simp add: permute_pure)

lemma supp_set_elem_finite:
  assumes "finite S"
  and "(m::'a::fs) \<in> S"
  and "y \<in> supp m"
  shows "y \<in> supp S"
  using assms supp_of_finite_sets
  by auto

lemmas fresh_star_Cons = fresh_star_list(2)

end
