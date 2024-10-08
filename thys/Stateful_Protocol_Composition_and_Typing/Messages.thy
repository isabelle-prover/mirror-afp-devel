(*  Title:      Messages.thy
    Author:     Andreas Viktor Hess, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section \<open>Protocol Messages as (First-Order) Terms\<close>

theory Messages
  imports Miscellaneous "First_Order_Terms.Term"
begin

subsection \<open>Term-related definitions: subterms and free variables\<close>
abbreviation "the_Fun \<equiv> un_Fun1"
lemmas the_Fun_def = un_Fun1_def

fun subterms::"('a,'b) term \<Rightarrow> ('a,'b) terms" where
  "subterms (Var x) = {Var x}"
| "subterms (Fun f T) = {Fun f T} \<union> (\<Union>t \<in> set T. subterms t)"

abbreviation subtermeq (infix \<open>\<sqsubseteq>\<close> 50) where "t' \<sqsubseteq> t \<equiv> (t' \<in> subterms t)"
abbreviation subterm (infix \<open>\<sqsubset>\<close> 50) where "t' \<sqsubset> t \<equiv> (t' \<sqsubseteq> t \<and> t' \<noteq> t)"

abbreviation "subterms\<^sub>s\<^sub>e\<^sub>t M \<equiv> \<Union>(subterms ` M)"
abbreviation subtermeqset (infix \<open>\<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t\<close> 50) where "t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t M \<equiv> (t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M)"

abbreviation fv where "fv \<equiv> vars_term"
lemmas fv_simps = term.simps(17,18)

fun fv\<^sub>s\<^sub>e\<^sub>t where "fv\<^sub>s\<^sub>e\<^sub>t M = \<Union>(fv ` M)"

abbreviation fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r where "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r p \<equiv> case p of (t,t') \<Rightarrow> fv t \<union> fv t'"

fun fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s where "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F = \<Union>(fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r ` set F)"

abbreviation ground where "ground M \<equiv> fv\<^sub>s\<^sub>e\<^sub>t M = {}"


subsection \<open>Variants that return lists insteads of sets\<close>
fun fv_list where
  "fv_list (Var x) = [x]"
| "fv_list (Fun f T) = concat (map fv_list T)"

definition fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s where
  "fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<equiv> concat (map (\<lambda>(t,t'). fv_list t@fv_list t') F)"

fun subterms_list::"('a,'b) term \<Rightarrow> ('a,'b) term list" where
  "subterms_list (Var x) = [Var x]"
| "subterms_list (Fun f T) = remdups (Fun f T#concat (map subterms_list T))"

lemma fv_list_is_fv: "fv t = set (fv_list t)"
by (induct t) auto

lemma fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_is_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F = set (fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F)"
by (induct F) (auto simp add: fv_list_is_fv fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_def)

lemma subterms_list_is_subterms: "subterms t = set (subterms_list t)"
by (induct t) auto


subsection \<open>The subterm relation defined as a function\<close>
fun subterm_of where
  "subterm_of t (Var y) = (t = Var y)"
| "subterm_of t (Fun f T) = (t = Fun f T \<or> list_ex (subterm_of t) T)"

lemma subterm_of_iff_subtermeq[code_unfold]: "t \<sqsubseteq> t' = subterm_of t t'"
proof (induction t')
  case (Fun f T) thus ?case
  proof (cases "t = Fun f T")
    case False thus ?thesis
      using Fun.IH subterm_of.simps(2)[of t f T]
      unfolding list_ex_iff by fastforce
  qed simp
qed simp

lemma subterm_of_ex_set_iff_subtermeqset[code_unfold]: "t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t M = (\<exists>t' \<in> M. subterm_of t t')"
using subterm_of_iff_subtermeq by blast


subsection \<open>The subterm relation is a partial order on terms\<close>
interpretation "term": order "(\<sqsubseteq>)" "(\<sqsubset>)"
proof
  show "s \<sqsubseteq> s" for s :: "('a,'b) term"
    by (induct s rule: subterms.induct) auto

  show trans: "s \<sqsubseteq> t \<Longrightarrow> t \<sqsubseteq> u \<Longrightarrow> s \<sqsubseteq> u" for s t u :: "('a,'b) term"
    by (induct u rule: subterms.induct) auto

  show "s \<sqsubseteq> t \<Longrightarrow> t \<sqsubseteq> s \<Longrightarrow> s = t" for s t :: "('a,'b) term"
  proof (induction s arbitrary: t rule: subterms.induct[case_names Var Fun])
    case (Fun f T)
    { assume 0: "t \<noteq> Fun f T"
      then obtain u::"('a,'b) term" where u: "u \<in> set T" "t \<sqsubseteq> u" using Fun.prems(2) by auto
      hence 1: "Fun f T \<sqsubseteq> u" using trans[OF Fun.prems(1)] by simp
   
      have 2: "u \<sqsubseteq> Fun f T"
        by (cases u) (use u(1) in force, use u(1) subterms.simps(2)[of f T] in fastforce)
      hence 3: "u = Fun f T" using Fun.IH[OF u(1) _ 1] by simp

      have "u \<sqsubseteq> t" using trans[OF 2 Fun.prems(1)] by simp
      hence 4: "u = t" using Fun.IH[OF u(1) _ u(2)] by simp
  
      have "t = Fun f T" using 3 4 by simp
      hence False using 0 by simp
    }
    thus ?case by auto
  qed simp
  thus "(s \<sqsubset> t) = (s \<sqsubseteq> t \<and> \<not>(t \<sqsubseteq> s))" for s t :: "('a,'b) term"
    by blast
qed


subsection \<open>Lemmata concerning subterms and free variables\<close>
lemma fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_append: "fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F@G) = fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F@fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G"
by (simp add: fv_list\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_def)

lemma distinct_fv_list_idx_fv_disjoint:
  assumes t: "distinct (fv_list t)" "Fun f T \<sqsubseteq> t"
    and ij: "i < length T" "j < length T" "i < j"
  shows "fv (T ! i) \<inter> fv (T ! j) = {}"
using t
proof (induction t rule: fv_list.induct)
  case (2 g S)
  have "distinct (fv_list s)" when s: "s \<in> set S" for s
    by (metis (no_types, lifting) s "2.prems"(1) concat_append distinct_append 
          map_append split_list fv_list.simps(2) concat.simps(2) list.simps(9))
  hence IH: "fv (T ! i) \<inter> fv (T ! j) = {}"
    when s: "s \<in> set S" "Fun f T \<sqsubseteq> s" for s
    using "2.IH" s by blast

  show ?case
  proof (cases "Fun f T = Fun g S")
    case True
    define U where "U \<equiv> map fv_list T"

    have a: "distinct (concat U)"
      using "2.prems"(1) True unfolding U_def by auto
    
    have b: "i < length U" "j < length U"
      using ij(1,2) unfolding U_def by simp_all

    show ?thesis
      using b distinct_concat_idx_disjoint[OF a b ij(3)]
            fv_list_is_fv[of "T ! i"] fv_list_is_fv[of "T ! j"]
      unfolding U_def by force
  qed (use IH "2.prems"(2) in auto)
qed force

lemma distinct_fv_list_Fun_param:
  assumes f: "distinct (fv_list (Fun f ts))"
    and t: "t \<in> set ts"
  shows "distinct (fv_list t)"
proof -
  obtain pre suf where "ts = pre@t#suf" using t by (meson split_list)
  thus ?thesis using distinct_append f by simp
qed

lemmas subtermeqI'[intro] = term.eq_refl

lemma subtermeqI''[intro]: "t \<in> set T \<Longrightarrow> t \<sqsubseteq> Fun f T"
by force

lemma finite_fv_set[intro]: "finite M \<Longrightarrow> finite (fv\<^sub>s\<^sub>e\<^sub>t M)"
by auto

lemma finite_fun_symbols[simp]: "finite (funs_term t)"
by (induct t) simp_all

lemma fv_set_mono: "M \<subseteq> N \<Longrightarrow> fv\<^sub>s\<^sub>e\<^sub>t M \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t N"
by auto

lemma subterms\<^sub>s\<^sub>e\<^sub>t_mono: "M \<subseteq> N \<Longrightarrow> subterms\<^sub>s\<^sub>e\<^sub>t M \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t N"
by auto

lemma ground_empty[simp]: "ground {}"
by simp

lemma ground_subset: "M \<subseteq> N \<Longrightarrow> ground N \<Longrightarrow> ground M"
by auto

lemma fv_map_fv_set: "\<Union>(set (map fv L)) = fv\<^sub>s\<^sub>e\<^sub>t (set L)"
by (induct L) auto

lemma fv\<^sub>s\<^sub>e\<^sub>t_union: "fv\<^sub>s\<^sub>e\<^sub>t (M \<union> N) = fv\<^sub>s\<^sub>e\<^sub>t M \<union> fv\<^sub>s\<^sub>e\<^sub>t N"
by auto

lemma finite_subset_Union:
  fixes A::"'a set" and f::"'a \<Rightarrow> 'b set"
  assumes "finite (\<Union>a \<in> A. f a)"
  shows "\<exists>B. finite B \<and> B \<subseteq> A \<and> (\<Union>b \<in> B. f b) = (\<Union>a \<in> A. f a)"
by (metis assms eq_iff finite_subset_image finite_UnionD)

lemma inv_set_fv: "finite M \<Longrightarrow> \<Union>(set (map fv (inv set M))) = fv\<^sub>s\<^sub>e\<^sub>t M"
using fv_map_fv_set[of "inv set M"] inv_set_fset by auto

lemma ground_subterm: "fv t = {} \<Longrightarrow> t' \<sqsubseteq> t \<Longrightarrow> fv t' = {}" by (induct t) auto

lemma empty_fv_not_var: "fv t = {} \<Longrightarrow> t \<noteq> Var x" by auto

lemma empty_fv_exists_fun: "fv t = {} \<Longrightarrow> \<exists>f X. t = Fun f X" by (cases t) auto

lemma vars_iff_subtermeq: "x \<in> fv t \<longleftrightarrow> Var x \<sqsubseteq> t" by (induct t) auto

lemma vars_iff_subtermeq_set: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<longleftrightarrow> Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t M"
using vars_iff_subtermeq[of x] by auto

lemma vars_if_subtermeq_set: "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<Longrightarrow> x \<in> fv\<^sub>s\<^sub>e\<^sub>t M"
by (metis vars_iff_subtermeq_set)

lemma subtermeq_set_if_vars: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<Longrightarrow> Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t M"
by (metis vars_iff_subtermeq_set)

lemma vars_iff_subterm_or_eq: "x \<in> fv t \<longleftrightarrow> Var x \<sqsubset> t \<or> Var x = t"
by (induct t) (auto simp add: vars_iff_subtermeq)

lemma var_is_subterm: "x \<in> fv t \<Longrightarrow> Var x \<in> subterms t"
by (simp add: vars_iff_subtermeq)

lemma subterm_is_var: "Var x \<in> subterms t \<Longrightarrow> x \<in> fv t"
by (simp add: vars_iff_subtermeq)

lemma no_var_subterm: "\<not>t \<sqsubset> Var v" by auto

lemma fun_if_subterm: "t \<sqsubset> u \<Longrightarrow> \<exists>f X. u = Fun f X" by (induct u) simp_all

lemma subtermeq_vars_subset: "M \<sqsubseteq> N \<Longrightarrow> fv M \<subseteq> fv N" by (induct N) auto

lemma fv_subterms[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (subterms t) = fv t"
by (induct t) auto

lemma fv_subterms_set[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (subterms\<^sub>s\<^sub>e\<^sub>t M) = fv\<^sub>s\<^sub>e\<^sub>t M"
using subtermeq_vars_subset by auto

lemma fv_subset: "t \<in> M \<Longrightarrow> fv t \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
by auto

lemma fv_subset_subterms: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<Longrightarrow> fv t \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
using fv_subset fv_subterms_set by metis

lemma subterms_finite[simp]: "finite (subterms t)" by (induction rule: subterms.induct) auto

lemma subterms_union_finite: "finite M \<Longrightarrow> finite (\<Union>t \<in> M. subterms t)"
by (induction rule: subterms.induct) auto

lemma subterms_subset: "t' \<sqsubseteq> t \<Longrightarrow> subterms t' \<subseteq> subterms t"
by (induction rule: subterms.induct) auto

lemma subterms_subset_set: "M \<subseteq> subterms t \<Longrightarrow> subterms\<^sub>s\<^sub>e\<^sub>t M \<subseteq> subterms t"
by (metis SUP_least contra_subsetD subterms_subset)

lemma subset_subterms_Union[simp]: "M \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t M" by auto

lemma in_subterms_Union: "t \<in> M \<Longrightarrow> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M" using subset_subterms_Union by blast

lemma in_subterms_subset_Union: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<Longrightarrow> subterms t \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t M"
using subterms_subset by auto

lemma subterm_param_split: 
  assumes "t \<sqsubset> Fun f X"
  shows "\<exists>pre x suf. t \<sqsubseteq> x \<and> X = pre@x#suf"
proof -
  obtain x where "t \<sqsubseteq> x" "x \<in> set X" using assms by auto
  then obtain pre suf where "X = pre@x#suf" "x \<notin> set pre \<or> x \<notin> set suf"
    by (meson split_list_first split_list_last)
  thus ?thesis using \<open>t \<sqsubseteq> x\<close> by auto
qed

lemma ground_iff_no_vars: "ground (M::('a,'b) terms) \<longleftrightarrow> (\<forall>v. Var v \<notin> (\<Union>m \<in> M. subterms m))"
proof
  assume "ground M"
  hence "\<forall>v. \<forall>m \<in> M. v \<notin> fv m" by auto
  hence "\<forall>v. \<forall>m \<in> M. Var v \<notin> subterms m" by (simp add: vars_iff_subtermeq)
  thus "(\<forall>v. Var v \<notin> (\<Union>m \<in> M. subterms m))" by simp
next
  assume no_vars: "\<forall>v. Var v \<notin> (\<Union>m \<in> M. subterms m)"
  moreover
  { assume "\<not>ground M"
    then obtain v and m::"('a,'b) term" where "m \<in> M" "fv m \<noteq> {}" "v \<in> fv m" by auto
    hence "Var v \<in> (subterms m)" by (simp add: vars_iff_subtermeq)
    hence "\<exists>v. Var v \<in> (\<Union>t \<in> M. subterms t)" using \<open>m \<in> M\<close> by auto
    hence False using no_vars by simp
  }
  ultimately show "ground M" by blast
qed

lemma index_Fun_subterms_subset[simp]: "i < length T \<Longrightarrow> subterms (T ! i) \<subseteq> subterms (Fun f T)"
by auto

lemma index_Fun_fv_subset[simp]: "i < length T \<Longrightarrow> fv (T ! i) \<subseteq> fv (Fun f T)"
using subtermeq_vars_subset by fastforce

lemma subterms_union_ground:
  assumes "ground M"
  shows "ground (subterms\<^sub>s\<^sub>e\<^sub>t M)"
proof -
  { fix t assume "t \<in> M"
    hence "fv t = {}"
      using ground_iff_no_vars[of M] assms
      by auto
    hence "\<forall>t' \<in> subterms t. fv t' = {}" using subtermeq_vars_subset[of _ t] by simp
    hence "ground (subterms t)" by auto
  }
  thus ?thesis by auto
qed

lemma Var_subtermeq: "t \<sqsubseteq> Var v \<Longrightarrow> t = Var v" by simp

lemma subtermeq_imp_funs_term_subset: "s \<sqsubseteq> t \<Longrightarrow> funs_term s \<subseteq> funs_term t"
by (induct t arbitrary: s) auto

lemma subterms_const: "subterms (Fun f []) = {Fun f []}" by simp

lemma subterm_subtermeq_neq: "\<lbrakk>t \<sqsubset> u; u \<sqsubseteq> v\<rbrakk> \<Longrightarrow> t \<noteq> v"
  using term.dual_order.strict_trans1 by blast 

lemma subtermeq_subterm_neq: "\<lbrakk>t \<sqsubseteq> u; u \<sqsubset> v\<rbrakk> \<Longrightarrow> t \<noteq> v"
by (metis term.order.eq_iff)

lemma subterm_size_lt: "x \<sqsubset> y \<Longrightarrow> size x < size y"
using not_less_eq size_list_estimation by (induct y, simp, fastforce)

lemma in_subterms_eq: "\<lbrakk>x \<in> subterms y; y \<in> subterms x\<rbrakk> \<Longrightarrow> subterms x = subterms y"
  using term.order.antisym by auto

lemma Fun_param_size_lt:
  "t \<in> set ts \<Longrightarrow> size t < size (Fun f ts)"
by (induct ts) auto

lemma Fun_zip_size_lt:
  assumes "(t,s) \<in> set (zip ts ss)"
  shows "size t < size (Fun f ts)"
    and "size s < size (Fun g ss)"
by (metis assms Fun_param_size_lt in_set_zipE)+

lemma Fun_gt_params: "Fun f X \<notin> (\<Union>x \<in> set X. subterms x)"
proof -
  have "size_list size X < size (Fun f X)" by simp
  hence "Fun f X \<notin> set X" by (meson less_not_refl size_list_estimation) 
  hence "\<forall>x \<in> set X. Fun f X \<notin> subterms x \<or> x \<notin> subterms (Fun f X)"
    using subtermeq_subterm_neq by blast 
  moreover have "\<forall>x \<in> set X. x \<in> subterms (Fun f X)" by fastforce
  ultimately show ?thesis by auto
qed

lemma params_subterms[simp]: "set X \<subseteq> subterms (Fun f X)" by auto

lemma params_subterms_Union[simp]: "subterms\<^sub>s\<^sub>e\<^sub>t (set X) \<subseteq> subterms (Fun f X)" by auto

lemma Fun_subterm_inside_params: "t \<sqsubset> Fun f X \<longleftrightarrow> t \<in> (\<Union>x \<in> (set X). subterms x)"
using Fun_gt_params by fastforce

lemma Fun_param_is_subterm: "x \<in> set X \<Longrightarrow> x \<sqsubset> Fun f X"
using Fun_subterm_inside_params by fastforce

lemma Fun_param_in_subterms: "x \<in> set X \<Longrightarrow> x \<in> subterms (Fun f X)"
using Fun_subterm_inside_params by fastforce

lemma Fun_not_in_param: "x \<in> set X \<Longrightarrow> \<not>Fun f X \<sqsubset> x"
  by (meson Fun_param_in_subterms term.less_le_not_le) 

lemma Fun_ex_if_subterm: "t \<sqsubset> s \<Longrightarrow> \<exists>f T. Fun f T \<sqsubseteq> s \<and> t \<in> set T"
proof (induction s)
  case (Fun f T)
  then obtain s' where s': "s' \<in> set T" "t \<sqsubseteq> s'" by auto
  show ?case
  proof (cases "t = s'")
    case True thus ?thesis using s' by blast
  next
    case False
    thus ?thesis
      using Fun.IH[OF s'(1)] s'(2) term.order_trans[OF _ Fun_param_in_subterms[OF s'(1), of f]]
      by metis
  qed
qed simp

lemma const_subterm_obtain:
  assumes "fv t = {}"
  obtains c where "Fun c [] \<sqsubseteq> t"
using assms
proof (induction t)
  case (Fun f T) thus ?case by (cases "T = []") force+
qed simp

lemma const_subterm_obtain': "fv t = {} \<Longrightarrow> \<exists>c. Fun c [] \<sqsubseteq> t"
by (metis const_subterm_obtain)

lemma subterms_singleton:
  assumes "(\<exists>v. t = Var v) \<or> (\<exists>f. t = Fun f [])"
  shows "subterms t = {t}"
using assms by (cases t) auto

lemma subtermeq_Var_const:
  assumes "s \<sqsubseteq> t"
  shows "t = Var v \<Longrightarrow> s = Var v" "t = Fun f [] \<Longrightarrow> s = Fun f []"
using assms by fastforce+

lemma subterms_singleton':
  assumes "subterms t = {t}"
  shows "(\<exists>v. t = Var v) \<or> (\<exists>f. t = Fun f [])"
proof (cases t)
  case (Fun f T)
  { fix s S assume "T = s#S"
    hence "s \<in> subterms t" using Fun by auto
    hence "s = t" using assms by auto
    hence False
      using Fun_param_is_subterm[of s "s#S" f] \<open>T = s#S\<close> Fun
      by auto
  }
  hence "T = []" by (cases T) auto
  thus ?thesis using Fun by simp
qed (simp add: assms)

lemma funs_term_subterms_eq[simp]:
  "(\<Union>s \<in> subterms t. funs_term s) = funs_term t" 
  "(\<Union>s \<in> subterms\<^sub>s\<^sub>e\<^sub>t M. funs_term s) = \<Union>(funs_term ` M)"
proof -
  show "\<And>t. \<Union>(funs_term ` subterms t) = funs_term t"
    using term.order_refl subtermeq_imp_funs_term_subset by blast
  thus "\<Union>(funs_term ` (subterms\<^sub>s\<^sub>e\<^sub>t M)) = \<Union>(funs_term ` M)" by force
qed

lemmas subtermI'[intro] = Fun_param_is_subterm

lemma funs_term_Fun_subterm: "f \<in> funs_term t \<Longrightarrow> \<exists>T. Fun f T \<in> subterms t"
proof (induction t)
  case (Fun g T)
  hence "f = g \<or> (\<exists>s \<in> set T. f \<in> funs_term s)" by simp
  thus ?case
  proof
    assume "\<exists>s \<in> set T. f \<in> funs_term s"
    then obtain s where "s \<in> set T" "\<exists>T. Fun f T \<in> subterms s" using Fun.IH by auto
    thus ?thesis by auto
  qed (auto simp add: Fun)
qed simp

lemma funs_term_Fun_subterm': "Fun f T \<in> subterms t \<Longrightarrow> f \<in> funs_term t"
by (induct t) auto

lemma zip_arg_subterm:
  assumes "(s,t) \<in> set (zip X Y)"
  shows "s \<sqsubset> Fun f X" "t \<sqsubset> Fun g Y"
proof -
  from assms have *: "s \<in> set X" "t \<in> set Y" by (meson in_set_zipE)+
  show "s \<sqsubset> Fun f X" by (metis Fun_param_is_subterm[OF *(1)])
  show "t \<sqsubset> Fun g Y" by (metis Fun_param_is_subterm[OF *(2)])
qed

lemma fv_disj_Fun_subterm_param_cases:
  assumes "fv t \<inter> X = {}" "Fun f T \<in> subterms t"
  shows "T = [] \<or> (\<exists>s\<in>set T. s \<notin> Var ` X)"
proof (cases T)
  case (Cons s S)
  hence "s \<in> subterms t"
    using assms(2) term.order_trans[of _ "Fun f T" t]
    by auto
  hence "fv s \<inter> X = {}" using assms(1) fv_subterms by force
  thus ?thesis using Cons by auto
qed simp

lemma fv_eq_FunI:
  assumes "length T = length S" "\<And>i. i < length T \<Longrightarrow> fv (T ! i) = fv (S ! i)"
  shows "fv (Fun f T) = fv (Fun g S)"
using assms
proof (induction T arbitrary: S)
  case (Cons t T S')
  then obtain s S where S': "S' = s#S" by (cases S') simp_all
  have "fv (T ! i) = fv (S ! i)" when "i < length T" for i
    using that Cons.prems(2)[of "Suc i"] unfolding S' by simp
  hence "fv (Fun f T) = fv (Fun g S)"
    using Cons.prems(1) Cons.IH[of S] unfolding S' by simp
  thus ?case using Cons.prems(2)[of 0] unfolding S' by auto
qed simp

lemma fv_eq_FunI':
  assumes "length T = length S" "\<And>i. i < length T \<Longrightarrow> x \<in> fv (T ! i) \<longleftrightarrow> x \<in> fv (S ! i)"
  shows "x \<in> fv (Fun f T) \<longleftrightarrow> x \<in> fv (Fun g S)"
using assms
proof (induction T arbitrary: S)
  case (Cons t T S')
  then obtain s S where S': "S' = s#S" by (cases S') simp_all
  show ?case using Cons.prems Cons.IH[of S] unfolding S' by fastforce
qed simp

lemma funs_term_eq_FunI:
  assumes "length T = length S" "\<And>i. i < length T \<Longrightarrow> funs_term (T ! i) = funs_term (S ! i)"
  shows "funs_term (Fun f T) = funs_term (Fun f S)"
using assms
proof (induction T arbitrary: S)
  case (Cons t T S')
  then obtain s S where S': "S' = s#S" by (cases S') simp_all
  have "funs_term (T ! i) = funs_term (S ! i)" when "i < length T" for i
    using that Cons.prems(2)[of "Suc i"] unfolding S' by simp
  hence "funs_term (Fun f T) = funs_term (Fun f S)"
    using Cons.prems(1) Cons.IH[of S] unfolding S' by simp
  thus ?case using Cons.prems(2)[of 0] unfolding S' by auto
qed simp

lemma finite_fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s[simp]: "finite (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s x)" by auto

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_Nil[simp]: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s [] = {}" by simp

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_singleton[simp]: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s [(t,s)] = fv t \<union> fv s" by simp

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_Cons: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ((s,t)#F) = fv s \<union> fv t \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F" by simp

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_append: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F@G) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<union> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G" by simp

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_mono: "set M \<subseteq> set N \<Longrightarrow> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s M \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s N" by auto

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_inI[intro]:
  "f \<in> set F \<Longrightarrow> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r f \<Longrightarrow> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
  "f \<in> set F \<Longrightarrow> x \<in> fv (fst f) \<Longrightarrow> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
  "f \<in> set F \<Longrightarrow> x \<in> fv (snd f) \<Longrightarrow> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
  "(t,s) \<in> set F \<Longrightarrow> x \<in> fv t \<Longrightarrow> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
  "(t,s) \<in> set F \<Longrightarrow> x \<in> fv s \<Longrightarrow> x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
using UN_I by fastforce+

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_cons_subset: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (f#F)"
by auto

lemma in_Fun_fv_iff_in_args_nth_fv:
  "x \<in> fv (Fun f ts) \<longleftrightarrow> (\<exists>i < length ts. x \<in> fv (ts ! i))"
  (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  hence "x \<in> \<Union>(fv ` set ts)" by auto
  thus ?B by (metis UN_E in_set_conv_nth)
qed auto


subsection \<open>Other lemmata\<close>
lemma nonvar_term_has_composed_shallow_term:
  fixes t::"('f,'v) term"
  assumes "\<not>(\<exists>x. t = Var x)"
  shows "\<exists>f T. Fun f T \<sqsubseteq> t \<and> (\<forall>s \<in> set T. (\<exists>c. s = Fun c []) \<or> (\<exists>x. s = Var x))"
proof -
  let ?Q = "\<lambda>S. \<forall>s \<in> set S. (\<exists>c. s = Fun c []) \<or> (\<exists>x. s = Var x)"
  let ?P = "\<lambda>t. \<exists>g S. Fun g S \<sqsubseteq> t \<and> ?Q S"
  { fix t::"('f,'v) term"
    have "(\<exists>x. t = Var x) \<or> ?P t"
    proof (induction t)
      case (Fun h R) show ?case
      proof (cases "R = [] \<or> (\<forall>r \<in> set R. \<exists>x. r = Var x)")
        case False
        then obtain r g S where "r \<in> set R" "?P r" "Fun g S \<sqsubseteq> r" "?Q S" using Fun.IH by fast
        thus ?thesis by auto
      qed force
    qed simp
  } thus ?thesis using assms by blast
qed

end
