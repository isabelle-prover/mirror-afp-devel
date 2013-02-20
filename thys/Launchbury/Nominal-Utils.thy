theory "Nominal-Utils"
imports "../Nominal2/Nominal2" "~~/src/HOL/Library/AList"
begin

subsubsection {* Lemmas helping with equivariance proofs *}

lemma perm_rel_lemma:
  assumes "\<And> \<pi> x y. r (\<pi> \<bullet> x) (\<pi> \<bullet> y) \<Longrightarrow> r x y"
  shows "r (\<pi> \<bullet> x) (\<pi> \<bullet> y) \<longleftrightarrow> r x y" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" by fact
next
  assume "r x y"
  hence "r (- \<pi> \<bullet> \<pi> \<bullet> x) (- \<pi> \<bullet> \<pi> \<bullet> y)" by simp
  thus "?l" by (rule assms)
qed

lemma eqvt_at_apply:
  assumes "eqvt_at f x"
  shows "(p \<bullet> f) x = f x"
by (metis (hide_lams, no_types) assms eqvt_at_def permute_fun_def permute_minus_cancel(1))

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

lemma option_case_eqvt[eqvt]:
  "\<pi> \<bullet> option_case d f x = option_case (\<pi> \<bullet> d) (\<pi> \<bullet> f) (\<pi> \<bullet> x)"
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

lemma fresh_star_Cons:
  "S \<sharp>* (x # xs) = (S \<sharp>* x \<and> S \<sharp>* xs)"
by (metis fresh_star_def fresh_Cons)

lemma fresh_star_append:
  shows "a \<sharp>* (xs @ ys) \<longleftrightarrow> a \<sharp>* xs \<and> a \<sharp>* ys"
by (metis fresh_star_def fresh_append)

lemma fresh_list_elem:
  assumes "a \<sharp> \<Gamma>"
  and "e \<in> set \<Gamma>"
  shows "a \<sharp> e"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma pure_fresh_star[simp]: "a \<sharp>* (x :: 'a :: pure)"
  by (simp add: fresh_star_def pure_fresh)

lemma supp_set_mem: "x \<in> set L \<Longrightarrow> supp x \<subseteq> supp L"
  by (induct L, auto simp add: supp_Cons)

subsubsection {* Freshness and support for subsets of variables *}

lemma supp_mono: "finite (B::'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> supp A \<subseteq> supp B"
  apply (subst (1 2) supp_finite_set_at_base)
  apply (auto dest:infinite_super)
  done

lemma fresh_subset:
  "finite B \<Longrightarrow> x \<sharp> (B :: 'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<sharp> A"
  by (auto dest:supp_mono simp add: fresh_def)

lemma fresh_star_subset:
  "finite B \<Longrightarrow> x \<sharp>* (B :: 'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<sharp>* A"
  by (metis fresh_star_def fresh_subset)

lemma fresh_star_set_subset:
  "x \<sharp>* (B :: 'a::at_base list) \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> x \<sharp>* A"
  by (metis fresh_star_set fresh_star_subset[OF finite_set])
end
