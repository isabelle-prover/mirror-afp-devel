(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
section \<open>Unification\<close>

subsection \<open>Unifiers\<close>

text \<open>Definition and properties of (most general) unifiers\<close>

theory Unifiers
  imports Term
begin

(*TODO: move*)
lemma map_eq_set_zipD [dest]:
  assumes "map f xs = map f ys"
    and "(x, y) \<in> set (zip xs ys)"
  shows "f x = f y"
using assms
proof (induct xs arbitrary: ys)
  case (Cons x xs)
  then show ?case by (cases ys) auto
qed simp

type_synonym ('f, 'v) equation = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'v) equations = "('f, 'v) equation set"

text \<open>The set of unifiers for a given set of equations.\<close>
definition unifiers :: "('f, 'v) equations \<Rightarrow> ('f, 'v) subst set"
  where
    "unifiers E = {\<sigma>. \<forall>p\<in>E. fst p \<cdot> \<sigma> = snd p \<cdot> \<sigma>}"

text \<open>Check whether a set of equations is unifiable.\<close>
definition "unifiable E \<longleftrightarrow> (\<exists>\<sigma>. \<sigma> \<in> unifiers E)"

lemma in_unifiersE [elim]:
  "\<lbrakk>\<sigma> \<in> unifiers E; (\<And>e. e \<in> E \<Longrightarrow> fst e \<cdot> \<sigma> = snd e \<cdot> \<sigma>) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (force simp: unifiers_def)

text \<open>Applying a substitution to a set of equations.\<close>
definition subst_set :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> ('f, 'v) equations"
  where
    "subst_set \<sigma> E = (\<lambda>e. (fst e \<cdot> \<sigma>, snd e \<cdot> \<sigma>)) ` E"

text \<open>Check whether a substitution is a most-general unifier (mgu) of a set of equations.\<close>
definition is_mgu :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool"
  where
    "is_mgu \<sigma> E \<longleftrightarrow> \<sigma> \<in> unifiers E \<and> (\<forall>\<tau> \<in> unifiers E. (\<exists>\<gamma>. \<tau> = \<sigma> \<circ>\<^sub>s \<gamma>))"

text \<open>The following property characterizes idempotent mgus, that is,
  mgus \<^term>\<open>\<sigma>\<close> for which \<^prop>\<open>\<sigma> \<circ>\<^sub>s \<sigma> = \<sigma>\<close> holds.\<close>
definition is_imgu :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool"
  where
    "is_imgu \<sigma> E \<longleftrightarrow> \<sigma> \<in> unifiers E \<and> (\<forall>\<tau> \<in> unifiers E. \<tau> = \<sigma> \<circ>\<^sub>s \<tau>)"


subsubsection \<open>Properties of sets of unifiers\<close>

lemma unifiers_Un [simp]:
  "unifiers (s \<union> t) = unifiers s \<inter> unifiers t"
  by (auto simp: unifiers_def)

lemma unifiers_empty [simp]:
  "unifiers {} = UNIV"
  by (auto simp: unifiers_def)

lemma unifiers_insert: (* "simp not added for readability (and termination)" *)
  "unifiers (insert p t) = {\<sigma>. fst p \<cdot> \<sigma> = snd p \<cdot> \<sigma>} \<inter> unifiers t"
  by (auto simp: unifiers_def)

lemma unifiers_insert_ident [simp]:
  "unifiers (insert (t, t) E) = unifiers E" 
  by (auto simp: unifiers_insert)

lemma unifiers_insert_swap:
  "unifiers (insert (s, t) E) = unifiers (insert (t, s) E)"
  by (auto simp: unifiers_insert)

lemma unifiers_insert_Var_swap [simp]:
  "unifiers (insert (t, Var x) E) = unifiers (insert (Var x, t) E)"
  by (rule unifiers_insert_swap)

lemma unifiers_subst_set [simp]:
  "\<tau> \<in> unifiers (subst_set \<sigma> E) \<longleftrightarrow> \<sigma> \<circ>\<^sub>s \<tau> \<in> unifiers E"
  by (auto simp: unifiers_def subst_set_def)

lemma unifiers_insert_VarD:
  shows "\<sigma> \<in> unifiers (insert (Var x, t) E) \<Longrightarrow> subst x t \<circ>\<^sub>s \<sigma> = \<sigma>"
    and "\<sigma> \<in> unifiers (insert (t, Var x) E) \<Longrightarrow> subst x t \<circ>\<^sub>s \<sigma> = \<sigma>"
  by (auto simp: unifiers_def)

lemma unifiers_insert_Var_left:
  "\<sigma> \<in> unifiers (insert (Var x, t) E) \<Longrightarrow> \<sigma> \<in> unifiers (subst_set (subst x t) E)"
  by (auto simp: unifiers_def subst_set_def)

lemma unifiers_set_zip [simp]:
  assumes "length ss = length ts"
  shows "unifiers (set (zip ss ts)) = {\<sigma>. map (\<lambda>t. t \<cdot> \<sigma>) ss = map (\<lambda>t. t \<cdot> \<sigma>) ts}"
  using assms by (induct ss ts rule: list_induct2) (auto simp: unifiers_def)

lemma unifiers_Fun [simp]:
  "\<sigma> \<in> unifiers {(Fun f ss, Fun g ts)} \<longleftrightarrow>
    length ss = length ts \<and> f = g \<and> \<sigma> \<in> unifiers (set (zip ss ts))"
  by (auto simp: unifiers_def dest: map_eq_imp_length_eq)
    (induct ss ts rule: list_induct2, simp_all)

lemma unifiers_occur_left_is_Fun:
  fixes t :: "('f, 'v) term"
  assumes "x \<in> vars_term t" and "is_Fun t"
  shows "unifiers (insert (Var x, t) E) = {}"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain \<sigma> :: "('f, 'v) subst" where "\<sigma> x = t \<cdot> \<sigma>" by (auto simp: unifiers_def)
  with is_Fun_num_funs_less [OF assms, of \<sigma>] show False by auto
qed

lemma unifiers_occur_left_not_Var:
  "x \<in> vars_term t \<Longrightarrow> t \<noteq> Var x \<Longrightarrow> unifiers (insert (Var x, t) E) = {}"
  using unifiers_occur_left_is_Fun [of x t] by (cases t) simp_all

lemma unifiers_occur_left_Fun:
  "x \<in> (\<Union>t\<in>set ts. vars_term t) \<Longrightarrow> unifiers (insert (Var x, Fun f ts) E) = {}"
  using unifiers_occur_left_is_Fun [of x "Fun f ts"] by simp

lemmas unifiers_occur_left_simps [simp] =
  unifiers_occur_left_is_Fun
  unifiers_occur_left_not_Var
  unifiers_occur_left_Fun


subsubsection \<open>Properties of unifiability\<close>

lemma in_vars_is_Fun_not_unifiable:
  assumes "x \<in> vars_term t" and "is_Fun t"
  shows "\<not> unifiable {(Var x, t)}"
proof
  assume "unifiable {(Var x, t)}"
  then obtain \<sigma> where "\<sigma> \<in> unifiers {(Var x, t)}"
    by (auto simp: unifiable_def)
  then have "\<sigma> x = t \<cdot> \<sigma>" by (auto)
  moreover have "num_funs (\<sigma> x) < num_funs (t \<cdot> \<sigma>)"
    using is_Fun_num_funs_less [OF assms] by auto
  ultimately show False by auto
qed

lemma unifiable_insert_swap:
  "unifiable (insert (s, t) E) = unifiable (insert (t, s) E)"
  by (auto simp: unifiable_def unifiers_insert_swap)

lemma subst_set_reflects_unifiable:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes "unifiable (subst_set \<sigma> E)"
  shows "unifiable E"
proof -
  { fix \<tau> :: "('f, 'v) subst" assume "\<forall>p\<in>E. fst p \<cdot> \<sigma> \<cdot> \<tau> = snd p \<cdot> \<sigma> \<cdot> \<tau>"
    then have "\<exists>\<sigma> :: ('f, 'v) subst. \<forall>p\<in>E. fst p \<cdot> \<sigma> = snd p \<cdot> \<sigma>"
      by (intro exI [of _ "\<sigma> \<circ>\<^sub>s \<tau>"]) auto }
  then show ?thesis using assms by (auto simp: unifiable_def unifiers_def subst_set_def)
qed


subsubsection \<open>Properties of \<^term>\<open>is_mgu\<close>\<close>

lemma is_mgu_empty [simp]:
  "is_mgu Var {}"
  by (auto simp: is_mgu_def)

lemma is_mgu_insert_trivial [simp]:
  "is_mgu \<sigma> (insert (t, t) E) = is_mgu \<sigma> E"
  by (auto simp: is_mgu_def)

lemma is_mgu_insert_decomp [simp]:
  assumes "length ss = length ts"
  shows "is_mgu \<sigma> (insert (Fun f ss, Fun f ts) E) \<longleftrightarrow>
    is_mgu \<sigma> (E \<union> set (zip ss ts))"
  using assms by (auto simp: is_mgu_def unifiers_insert)

lemma is_mgu_insert_swap:
  "is_mgu \<sigma> (insert (s, t) E) = is_mgu \<sigma> (insert (t, s) E)"
  by (auto simp: is_mgu_def unifiers_def)

lemma is_mgu_insert_Var_swap [simp]:
  "is_mgu \<sigma> (insert (t, Var x) E) = is_mgu \<sigma> (insert (Var x, t) E)"
  by (rule is_mgu_insert_swap)

lemma is_mgu_subst_set_subst:
  assumes "x \<notin> vars_term t"
    and "is_mgu \<sigma> (subst_set (subst x t) E)" (is "is_mgu \<sigma> ?E")
  shows "is_mgu (subst x t \<circ>\<^sub>s \<sigma>) (insert (Var x, t) E)" (is "is_mgu ?\<sigma> ?E'")
proof -
  from \<open>is_mgu \<sigma> ?E\<close>
    have "?\<sigma> \<in> unifiers E"
    and *: "\<forall>\<tau>. (subst x t \<circ>\<^sub>s \<tau>) \<in> unifiers E \<longrightarrow> (\<exists>\<mu>. \<tau> = \<sigma> \<circ>\<^sub>s \<mu>)"
    by (auto simp: is_mgu_def)
  then have "?\<sigma> \<in> unifiers ?E'" using assms by (simp add: unifiers_insert subst_compose)
  moreover have "\<forall>\<tau>. \<tau> \<in> unifiers ?E' \<longrightarrow> (\<exists>\<mu>. \<tau> = ?\<sigma> \<circ>\<^sub>s \<mu>)"
  proof (intro allI impI)
    fix \<tau>
    assume **: "\<tau> \<in> unifiers ?E'"
    then have [simp]: "subst x t \<circ>\<^sub>s \<tau> = \<tau>" by (blast dest: unifiers_insert_VarD)
    from unifiers_insert_Var_left [OF **]
      have "subst x t \<circ>\<^sub>s \<tau> \<in> unifiers E" by (simp)
    with * obtain \<mu> where "\<tau> = \<sigma> \<circ>\<^sub>s \<mu>" by blast
    then have "subst x t \<circ>\<^sub>s \<tau> = subst x t \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<mu>" by (auto simp: ac_simps)
    then show "\<exists>\<mu>. \<tau> = subst x t \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<mu>" by auto
  qed
  ultimately show "is_mgu ?\<sigma> ?E'" by (simp add: is_mgu_def)
qed

lemma is_imgu_imp_is_mgu:
  assumes "is_imgu \<sigma> E"
  shows "is_mgu \<sigma> E"
  using assms by (auto simp: is_imgu_def is_mgu_def)


subsubsection \<open>Properties of \<^term>\<open>is_imgu\<close>\<close>

lemma rename_subst_domain_range_preserves_is_imgu: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes E :: "('f, 'v) equations" and \<mu> \<rho> :: "('f, 'v) subst"
  assumes imgu_\<mu>: "is_imgu \<mu> E" and is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "is_imgu (rename_subst_domain_range \<rho> \<mu>) (subst_set \<rho> E)"
proof (unfold is_imgu_def, intro conjI ballI)
  from imgu_\<mu> have unif_\<mu>: "\<mu> \<in> unifiers E"
    by (simp add: is_imgu_def)

  show "rename_subst_domain_range \<rho> \<mu> \<in> unifiers (subst_set \<rho> E)"
    unfolding unifiers_subst_set unifiers_def mem_Collect_eq
  proof (rule ballI)
    fix e\<^sub>\<rho> assume "e\<^sub>\<rho> \<in> subst_set \<rho> E"
    then obtain e where "e \<in> E" and "e\<^sub>\<rho> = (fst e \<cdot> \<rho>, snd e \<cdot> \<rho>)"
      by (auto simp: subst_set_def)
    then show "fst e\<^sub>\<rho> \<cdot> rename_subst_domain_range \<rho> \<mu> = snd e\<^sub>\<rho> \<cdot> rename_subst_domain_range \<rho> \<mu>"
      using unif_\<mu> subst_apply_term_renaming_rename_subst_domain_range[OF is_var_\<rho> \<open>inj \<rho>\<close>, of _ \<mu>]
      by (simp add: unifiers_def)
  qed
next
  fix \<upsilon> :: "('f, 'v) subst"
  assume "\<upsilon> \<in> unifiers (subst_set \<rho> E)"
  hence "(\<rho> \<circ>\<^sub>s \<upsilon>) \<in> unifiers E"
    by (simp add: subst_set_def unifiers_def)
  with imgu_\<mu> have \<mu>_\<rho>_\<upsilon>: "\<mu> \<circ>\<^sub>s \<rho> \<circ>\<^sub>s \<upsilon> = \<rho> \<circ>\<^sub>s \<upsilon>"
    by (simp add: is_imgu_def subst_compose_assoc)

  show "\<upsilon> = rename_subst_domain_range \<rho> \<mu> \<circ>\<^sub>s \<upsilon>"
  proof (rule ext)
    fix x
    show "\<upsilon> x = (rename_subst_domain_range \<rho> \<mu> \<circ>\<^sub>s \<upsilon>) x"
    proof (cases "Var x \<in> \<rho> ` subst_domain \<mu>")
      case True
      hence "(rename_subst_domain_range \<rho> \<mu> \<circ>\<^sub>s \<upsilon>) x = (\<mu> \<circ>\<^sub>s \<rho> \<circ>\<^sub>s \<upsilon>) (the_inv \<rho> (Var x))"
        by (simp add: rename_subst_domain_range_def subst_compose_def)
      also have "\<dots> = (\<rho> \<circ>\<^sub>s \<upsilon>) (the_inv \<rho> (Var x))"
        by (simp add: \<mu>_\<rho>_\<upsilon>)
      also have "\<dots> = (\<rho> (the_inv \<rho> (Var x))) \<cdot> \<upsilon>"
        by (simp add: subst_compose)
      also have "\<dots> = Var x \<cdot> \<upsilon>"
        using True f_the_inv_into_f[OF \<open>inj \<rho>\<close>, of "Var x"] by force
      finally show ?thesis
        by simp
    next
      case False
      thus ?thesis
        by (simp add: rename_subst_domain_range_def subst_compose)
    qed
  qed
qed

corollary rename_subst_domain_range_preserves_is_imgu_singleton: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  fixes t u :: "('f, 'v) term" and \<mu> \<rho> :: "('f, 'v) subst"
  assumes imgu_\<mu>: "is_imgu \<mu> {(t, u)}" and is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
  shows "is_imgu (rename_subst_domain_range \<rho> \<mu>) {(t \<cdot> \<rho>, u \<cdot> \<rho>)}"
  by (rule rename_subst_domain_range_preserves_is_imgu[OF imgu_\<mu> is_var_\<rho> \<open>inj \<rho>\<close>,
        unfolded subst_set_def, simplified])

end
