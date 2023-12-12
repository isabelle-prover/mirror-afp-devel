section \<open>Soundness\<close>

theory Soundness
  imports
    Elementary_Logic
    Semantics
begin

no_notation funcset (infixr "\<rightarrow>" 60)
notation funcset (infixr "\<Zpfun>" 60)

subsection \<open>Proposition 5400\<close>

proposition (in general_model) prop_5400:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "\<phi> \<leadsto> \<D>" and "\<psi> \<leadsto> \<D>"
  and "\<forall>v \<in> free_vars A. \<phi> v = \<psi> v"
  shows "\<V> \<phi> A = \<V> \<psi> A"
proof -
  from assms(1) show ?thesis
  using assms(2,3,4) proof (induction A arbitrary: \<phi> \<psi>)
    case (var_is_wff \<alpha> x)
    have "(x, \<alpha>) \<in> free_vars (x\<^bsub>\<alpha>\<^esub>)"
      by simp
    from assms(1) and var_is_wff.prems(1) have "\<V> \<phi> (x\<^bsub>\<alpha>\<^esub>) = \<phi> (x, \<alpha>)"
      using \<V>_is_wff_denotation_function by fastforce
    also from \<open>(x, \<alpha>) \<in> free_vars (x\<^bsub>\<alpha>\<^esub>)\<close> and var_is_wff.prems(3) have "\<dots> = \<psi> (x, \<alpha>)"
      by (simp only:)
    also from assms(1) and var_is_wff.prems(2) have "\<dots> = \<V> \<psi> (x\<^bsub>\<alpha>\<^esub>)"
      using \<V>_is_wff_denotation_function by fastforce
    finally show ?case .
  next
    case (con_is_wff \<alpha> c)
    from assms(1) and con_is_wff.prems(1) have "\<V> \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = \<J> (c, \<alpha>)"
      using \<V>_is_wff_denotation_function by fastforce
    also from assms(1) and con_is_wff.prems(2) have "\<dots> = \<V> \<psi> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>)"
      using \<V>_is_wff_denotation_function by fastforce
    finally show ?case .
  next
    case (app_is_wff \<alpha> \<beta> A B)
    have "free_vars (A \<sqdot> B) = free_vars A \<union> free_vars B"
      by simp
    with app_is_wff.prems(3)
    have "\<forall>v \<in> free_vars A. \<phi> v = \<psi> v" and "\<forall>v \<in> free_vars B. \<phi> v = \<psi> v"
      by blast+
    with app_is_wff.IH and app_is_wff.prems(1,2) have "\<V> \<phi> A = \<V> \<psi> A" and "\<V> \<phi> B = \<V> \<psi> B"
      by blast+
    from assms(1) and app_is_wff.prems(1) and app_is_wff.hyps have "\<V> \<phi> (A \<sqdot> B) = \<V> \<phi> A \<bullet> \<V> \<phi> B"
      using \<V>_is_wff_denotation_function by fastforce
    also from \<open>\<V> \<phi> A = \<V> \<psi> A\<close> and \<open>\<V> \<phi> B = \<V> \<psi> B\<close> have "\<dots> = \<V> \<psi> A \<bullet> \<V> \<psi> B"
      by (simp only:)
    also from assms(1) and app_is_wff.prems(2) and app_is_wff.hyps have "\<dots> = \<V> \<psi> (A \<sqdot> B)"
      using \<V>_is_wff_denotation_function by fastforce
    finally show ?case .
  next
    case (abs_is_wff \<beta> A \<alpha> x)
    have "free_vars (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = free_vars A - {(x, \<alpha>)}"
      by simp
    with abs_is_wff.prems(3) have "\<forall>v \<in> free_vars A. v \<noteq> (x, \<alpha>)\<longrightarrow> \<phi> v = \<psi> v"
      by blast
    then have "\<forall>v \<in> free_vars A. (\<phi>((x, \<alpha>) := z)) v = (\<psi>((x, \<alpha>) := z)) v" if "z \<in> elts (\<D> \<alpha>)" for z
      by simp
    moreover from abs_is_wff.prems(1,2)
    have "\<forall>x' \<alpha>'. (\<phi>((x, \<alpha>) := z)) (x', \<alpha>') \<in> elts (\<D> \<alpha>')" (* needs \<alpha>-conversion *)
      and "\<forall>x' \<alpha>'. (\<psi>((x, \<alpha>) := z)) (x', \<alpha>') \<in> elts (\<D> \<alpha>')" (* needs \<alpha>-conversion *)
      if "z \<in> elts (\<D> \<alpha>)" for z
      using that by force+
    ultimately have \<V>_\<phi>_\<psi>_eq: "\<V> (\<phi>((x, \<alpha>) := z)) A = \<V> (\<psi>((x, \<alpha>) := z)) A" if "z \<in> elts (\<D> \<alpha>)" for z
      using abs_is_wff.IH and that by simp
    from assms(1) and abs_is_wff.prems(1) and abs_is_wff.hyps
    have "\<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = (\<^bold>\<lambda>z \<^bold>: \<D> \<alpha>\<^bold>. \<V> (\<phi>((x, \<alpha>) := z)) A)"
      using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by simp
    also from \<V>_\<phi>_\<psi>_eq have "\<dots> = (\<^bold>\<lambda>z \<^bold>: \<D> \<alpha>\<^bold>. \<V> (\<psi>((x, \<alpha>) := z)) A)"
      by (fact vlambda_extensionality)
    also from assms(1) and abs_is_wff.hyps have "\<dots> = \<V> \<psi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
      using wff_abs_denotation[OF \<V>_is_wff_denotation_function abs_is_wff.prems(2)] by simp
    finally show ?case .
  qed
qed

corollary (in general_model) closed_wff_is_meaningful_regardless_of_assignment:
  assumes "is_closed_wff_of_type A \<alpha>"
  and "\<phi> \<leadsto> \<D>" and "\<psi> \<leadsto> \<D>"
  shows "\<V> \<phi> A = \<V> \<psi> A"
  using assms and prop_5400 by blast

subsection \<open>Proposition 5401\<close>

lemma (in general_model) prop_5401_a:
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  shows "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) = \<V> (\<phi>((x, \<alpha>) := \<V> \<phi> A)) B"
proof -
  from assms(2,3) have "\<lambda>x\<^bsub>\<alpha>\<^esub>. B \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>"
    by blast
  with assms(1,2) have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) = \<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<bullet> \<V> \<phi> A"
    using \<V>_is_wff_denotation_function by blast
  also from assms(1,3) have "\<dots> = app (\<^bold>\<lambda>z \<^bold>: \<D> \<alpha>\<^bold>. \<V> (\<phi>((x, \<alpha>) := z)) B) (\<V> \<phi> A)"
    using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by simp
  also from assms(1,2) have "\<dots> = \<V> (\<phi>((x, \<alpha>) := \<V> \<phi> A)) B"
    using \<V>_is_wff_denotation_function by auto
  finally show ?thesis .
qed

lemma (in general_model) prop_5401_b:
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<V> \<phi> (A =\<^bsub>\<alpha>\<^esub> B) = \<^bold>T \<longleftrightarrow> \<V> \<phi> A = \<V> \<phi> B"
proof -
  from assms have "{\<V> \<phi> A, \<V> \<phi> B} \<subseteq> elts (\<D> \<alpha>)"
    using \<V>_is_wff_denotation_function by auto
  have "\<V> \<phi> (A =\<^bsub>\<alpha>\<^esub> B) = \<V> \<phi> (Q\<^bsub>\<alpha>\<^esub> \<sqdot> A \<sqdot> B)"
    by simp
  also from assms have "\<dots> = \<V> \<phi> (Q\<^bsub>\<alpha>\<^esub> \<sqdot> A) \<bullet> \<V> \<phi> B"
    using \<V>_is_wff_denotation_function by blast
  also from assms have "\<dots> = \<V> \<phi> (Q\<^bsub>\<alpha>\<^esub>) \<bullet> \<V> \<phi> A \<bullet> \<V> \<phi> B"
    using Q_wff and wff_app_denotation[OF \<V>_is_wff_denotation_function] by fastforce
  also from assms(1) have "\<dots> = (q\<^bsub>\<alpha>\<^esub>) \<bullet> \<V> \<phi> A \<bullet> \<V> \<phi> B"
    using Q_denotation and \<V>_is_wff_denotation_function by fastforce
  also from \<open>{\<V> \<phi> A, \<V> \<phi> B} \<subseteq> elts (\<D> \<alpha>)\<close> have "\<dots> = \<^bold>T \<longleftrightarrow> \<V> \<phi> A = \<V> \<phi> B"
    using q_is_equality by simp
  finally show ?thesis .
qed

corollary (in general_model) prop_5401_b':
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>o\<^esub>"
  and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "\<V> \<phi> (A \<equiv>\<^sup>\<Q> B) = \<^bold>T \<longleftrightarrow> \<V> \<phi> A = \<V> \<phi> B"
  using assms and prop_5401_b by auto

lemma (in general_model) prop_5401_c:
  assumes "\<phi> \<leadsto> \<D>"
  shows "\<V> \<phi> T\<^bsub>o\<^esub> = \<^bold>T"
proof -
  have "Q\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>"
    by blast
  moreover have "\<V> \<phi> T\<^bsub>o\<^esub> = \<V> \<phi> (Q\<^bsub>o\<^esub> =\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> Q\<^bsub>o\<^esub>)"
    unfolding true_def ..
  ultimately have "\<dots> = \<^bold>T \<longleftrightarrow> \<V> \<phi> (Q\<^bsub>o\<^esub>) = \<V> \<phi> (Q\<^bsub>o\<^esub>)"
    using prop_5401_b and assms by blast
  then show ?thesis
    by simp
qed

lemma (in general_model) prop_5401_d:
  assumes "\<phi> \<leadsto> \<D>"
  shows "\<V> \<phi> F\<^bsub>o\<^esub> = \<^bold>F"
proof -
  have "\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>" and "\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by blast+
  moreover have "\<V> \<phi> F\<^bsub>o\<^esub> = \<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub> =\<^bsub>o\<rightarrow>o\<^esub> \<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>)"
    unfolding false_def ..
  ultimately have "\<V> \<phi> F\<^bsub>o\<^esub> = \<^bold>T \<longleftrightarrow> \<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) = \<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>)"
    using prop_5401_b and assms by simp
  moreover have "\<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) \<noteq> \<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>)"
  proof -
    have "\<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) = (\<^bold>\<lambda>z \<^bold>: \<D> o\<^bold>. \<^bold>T)"
    proof -
      from assms have T_denotation: "\<V> (\<phi>((\<xx>, o) := z)) T\<^bsub>o\<^esub> = \<^bold>T" if "z \<in> elts (\<D> o)" for z
        using prop_5401_c and that by simp
      from assms have "\<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. T\<^bsub>o\<^esub>) = (\<^bold>\<lambda>z \<^bold>: \<D> o\<^bold>. \<V> (\<phi>((\<xx>, o) := z)) T\<^bsub>o\<^esub>)"
        using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by blast
      also from assms and T_denotation have "\<dots> = (\<^bold>\<lambda>z \<^bold>: \<D> o\<^bold>. \<^bold>T)"
        using vlambda_extensionality by fastforce
      finally show ?thesis .
    qed
    moreover have "\<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) = (\<^bold>\<lambda>z \<^bold>: \<D> o\<^bold>. z)"
    proof -
      from assms have \<xx>_denotation: "\<V> (\<phi>((\<xx>, o) := z)) (\<xx>\<^bsub>o\<^esub>) = z" if "z \<in> elts (\<D> o)" for z
        using that and \<V>_is_wff_denotation_function by auto
      from assms have "\<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) = (\<^bold>\<lambda>z \<^bold>: \<D> o\<^bold>. \<V> (\<phi>((\<xx>, o) := z)) (\<xx>\<^bsub>o\<^esub>))"
        using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by blast
      also from \<xx>_denotation have "\<dots> = (\<^bold>\<lambda>z \<^bold>: (\<D> o)\<^bold>. z)"
        using vlambda_extensionality by fastforce
      finally show ?thesis .
    qed
    moreover have "(\<^bold>\<lambda>z \<^bold>: \<D> o\<^bold>. \<^bold>T) \<noteq> (\<^bold>\<lambda>z \<^bold>: \<D> o\<^bold>. z)"
    proof -
      from assms(1) have "(\<^bold>\<lambda>z \<^bold>: \<D> o\<^bold>. \<^bold>T) \<bullet> \<^bold>F = \<^bold>T"
        by (simp add: truth_values_domain_def)
      moreover from assms(1) have "(\<^bold>\<lambda>z \<^bold>: \<D> o\<^bold>. z) \<bullet> \<^bold>F = \<^bold>F"
        by (simp add: truth_values_domain_def)
      ultimately show ?thesis
        by (auto simp add: inj_eq)
    qed
    ultimately show ?thesis
      by simp
  qed
  moreover from assms have "\<V> \<phi> F\<^bsub>o\<^esub> \<in> elts (\<D> o)"
    using false_wff and \<V>_is_wff_denotation_function by fast
  ultimately show ?thesis
    using assms(1) by (simp add: truth_values_domain_def)
qed

lemma (in general_model) prop_5401_e:
  assumes "\<phi> \<leadsto> \<D>"
  and "{x, y} \<subseteq> elts (\<D> o)"
  shows "\<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y = (if x = \<^bold>T \<and> y = \<^bold>T then \<^bold>T else \<^bold>F)"
proof -
  let ?B\<^sub>l\<^sub>e\<^sub>q = "\<lambda>\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<sqdot> T\<^bsub>o\<^esub>"
  let ?B\<^sub>r\<^sub>e\<^sub>q = "\<lambda>\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<sqdot> \<yy>\<^bsub>o\<^esub>"
  let ?B\<^sub>e\<^sub>q = "?B\<^sub>l\<^sub>e\<^sub>q =\<^bsub>(o\<rightarrow>o\<rightarrow>o)\<rightarrow>o\<^esub> ?B\<^sub>r\<^sub>e\<^sub>q"
  let ?B\<^sub>\<yy> = "\<lambda>\<yy>\<^bsub>o\<^esub>. ?B\<^sub>e\<^sub>q"
  let ?B\<^sub>\<xx> = "\<lambda>\<xx>\<^bsub>o\<^esub>. ?B\<^sub>\<yy>"
  let ?\<phi>' = "\<phi>((\<xx>, o) := x, (\<yy>, o) := y)"
  let ?\<phi>'' = "\<lambda>g. ?\<phi>'((\<gg>, o\<rightarrow>o\<rightarrow>o) := g)"
  have "\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by blast
  have "\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>" and "\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<sqdot> \<yy>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
    by blast+
  have "?B\<^sub>l\<^sub>e\<^sub>q \<in> wffs\<^bsub>(o\<rightarrow>o\<rightarrow>o)\<rightarrow>o\<^esub>" and "?B\<^sub>r\<^sub>e\<^sub>q \<in> wffs\<^bsub>(o\<rightarrow>o\<rightarrow>o)\<rightarrow>o\<^esub>"
    by blast+
  then have "?B\<^sub>e\<^sub>q \<in> wffs\<^bsub>o\<^esub>" and "?B\<^sub>\<yy> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>" and "?B\<^sub>\<xx> \<in> wffs\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>"
    by blast+
  have "\<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y = \<V> \<phi> ?B\<^sub>\<xx> \<bullet> x \<bullet> y"
    by simp
  also from assms and \<open>?B\<^sub>\<yy> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> have "\<dots> = \<V> (\<phi>((\<xx>, o) := x)) ?B\<^sub>\<yy> \<bullet> y"
    using mixed_beta_conversion by simp
  also from assms and \<open>?B\<^sub>e\<^sub>q \<in> wffs\<^bsub>o\<^esub>\<close> have "\<dots> = \<V> ?\<phi>' ?B\<^sub>e\<^sub>q"
    using mixed_beta_conversion by simp
  finally have "\<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y = \<^bold>T \<longleftrightarrow> \<V> ?\<phi>' ?B\<^sub>l\<^sub>e\<^sub>q = \<V> ?\<phi>' ?B\<^sub>r\<^sub>e\<^sub>q"
    using assms and \<open>?B\<^sub>l\<^sub>e\<^sub>q \<in> wffs\<^bsub>(o\<rightarrow>o\<rightarrow>o)\<rightarrow>o\<^esub>\<close> and \<open>?B\<^sub>r\<^sub>e\<^sub>q \<in> wffs\<^bsub>(o\<rightarrow>o\<rightarrow>o)\<rightarrow>o\<^esub>\<close> and prop_5401_b
    by simp
  also have "\<dots> \<longleftrightarrow> (\<^bold>\<lambda>g \<^bold>: \<D> (o\<rightarrow>o\<rightarrow>o)\<^bold>. g \<bullet> \<^bold>T \<bullet> \<^bold>T) = (\<^bold>\<lambda>g \<^bold>: \<D> (o\<rightarrow>o\<rightarrow>o)\<^bold>. g \<bullet> x \<bullet> y)"
  proof -
    have leq: "\<V> ?\<phi>' ?B\<^sub>l\<^sub>e\<^sub>q = (\<^bold>\<lambda>g \<^bold>: \<D> (o\<rightarrow>o\<rightarrow>o)\<^bold>. g \<bullet> \<^bold>T \<bullet> \<^bold>T)"
    and req: "\<V> ?\<phi>' ?B\<^sub>r\<^sub>e\<^sub>q = (\<^bold>\<lambda>g \<^bold>: \<D> (o\<rightarrow>o\<rightarrow>o)\<^bold>. g \<bullet> x \<bullet> y)"
    proof -
      from assms(1,2) have is_assg_\<phi>'': "?\<phi>'' g \<leadsto> \<D>" if "g \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o))" for g
        using that by auto
      have side_eq_denotation:
        "\<V> ?\<phi>' (\<lambda>\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B) = (\<^bold>\<lambda>g \<^bold>: \<D> (o\<rightarrow>o\<rightarrow>o)\<^bold>. g \<bullet> \<V> (?\<phi>'' g) A \<bullet> \<V> (?\<phi>'' g) B)"
        if "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>" for A and B
      proof -
        from that have "\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B \<in> wffs\<^bsub>o\<^esub>"
          by blast
        have "\<V> (?\<phi>'' g) (\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B) = g \<bullet> \<V> (?\<phi>'' g) A \<bullet> \<V> (?\<phi>'' g) B"
          if "g \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o))" for g
        proof -
          from \<open>A \<in> wffs\<^bsub>o\<^esub>\<close> have "\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
            by blast
          with that and is_assg_\<phi>'' and \<open>B \<in> wffs\<^bsub>o\<^esub>\<close> have "
            \<V> (?\<phi>'' g) (\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B) = \<V> (?\<phi>'' g) (\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A) \<bullet> \<V> (?\<phi>'' g) B"
            using wff_app_denotation[OF \<V>_is_wff_denotation_function] by simp
          also from that and \<open>A \<in> wffs\<^bsub>o\<^esub>\<close> and is_assg_\<phi>'' have "
            \<dots> = \<V> (?\<phi>'' g) (\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> \<V> (?\<phi>'' g) A \<bullet> \<V> (?\<phi>'' g) B"
            by (metis \<V>_is_wff_denotation_function wff_app_denotation wffs_of_type_intros(1))
          finally show ?thesis
            using that and is_assg_\<phi>'' and \<V>_is_wff_denotation_function by auto
        qed
        moreover from assms have "is_assignment ?\<phi>'"
          by auto
        with \<open>\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B \<in> wffs\<^bsub>o\<^esub>\<close> have "
          \<V> ?\<phi>' (\<lambda>\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B) = (\<^bold>\<lambda>g \<^bold>: \<D> (o\<rightarrow>o\<rightarrow>o)\<^bold>. \<V> (?\<phi>'' g) (\<gg>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B))"
          using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by simp
        ultimately show ?thesis
          using vlambda_extensionality by fastforce
      qed
      \<comment> \<open>Proof of \<open>leq\<close>:\<close>
      show "\<V> ?\<phi>' ?B\<^sub>l\<^sub>e\<^sub>q = (\<^bold>\<lambda>g \<^bold>: \<D> (o\<rightarrow>o\<rightarrow>o)\<^bold>. g \<bullet> \<^bold>T \<bullet> \<^bold>T)"
      proof -
        have "\<V> (?\<phi>'' g) T\<^bsub>o\<^esub> = \<^bold>T" if "g \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o))" for g
          using that and is_assg_\<phi>'' and prop_5401_c by simp
        then show ?thesis
          using side_eq_denotation and true_wff and vlambda_extensionality by fastforce
      qed
      \<comment> \<open>Proof of \<open>req\<close>:\<close>
      show "\<V> ?\<phi>' ?B\<^sub>r\<^sub>e\<^sub>q = (\<^bold>\<lambda>g \<^bold>: \<D> (o\<rightarrow>o\<rightarrow>o)\<^bold>. g \<bullet> x \<bullet> y)"
      proof -
        from is_assg_\<phi>'' have "\<V> (?\<phi>'' g) (\<xx>\<^bsub>o\<^esub>) = x" and "\<V> (?\<phi>'' g) (\<yy>\<^bsub>o\<^esub>) = y"
          if "g \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o))" for g
          using that and \<V>_is_wff_denotation_function by auto
        with side_eq_denotation show ?thesis
          using wffs_of_type_intros(1) and vlambda_extensionality by fastforce
      qed
    qed
    then show ?thesis
      by auto
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>g \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o)). g \<bullet> \<^bold>T \<bullet> \<^bold>T = g \<bullet> x \<bullet> y)"
    using vlambda_extensionality and VLambda_eq_D2 by fastforce
  finally have and_eqv: "
    \<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y = \<^bold>T \<longleftrightarrow> (\<forall>g \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o)). g \<bullet> \<^bold>T \<bullet> \<^bold>T = g \<bullet> x \<bullet> y)"
    by blast
  then show ?thesis
  proof -
    from assms(1,2) have is_assg_1: "\<phi>((\<xx>, o) := \<^bold>T) \<leadsto> \<D>"
      by (simp add: truth_values_domain_def)
    then have is_assg_2: "\<phi>((\<xx>, o) := \<^bold>T, (\<yy>, o) := \<^bold>T) \<leadsto> \<D>"
      unfolding is_assignment_def by (metis fun_upd_apply prod.sel(2))
    from assms consider (a) "x = \<^bold>T \<and> y = \<^bold>T" | (b) "x \<noteq> \<^bold>T" | (c) "y \<noteq> \<^bold>T"
      by blast
    then show ?thesis
    proof cases
      case a
      then have "g \<bullet> \<^bold>T \<bullet> \<^bold>T = g \<bullet> x \<bullet> y" if "g \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o))" for g
        by simp
      with a and and_eqv show ?thesis
        by simp
    next
      case b
      let ?g_witness = "\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>"
      have "\<lambda>\<yy>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
        by blast
      then have "is_closed_wff_of_type ?g_witness (o\<rightarrow>o\<rightarrow>o)"
        by force
      moreover from assms have is_assg_\<phi>': "?\<phi>' \<leadsto> \<D>"
        by simp
      ultimately have "\<V> \<phi> ?g_witness \<bullet> \<^bold>T \<bullet> \<^bold>T = \<V> ?\<phi>' ?g_witness \<bullet> \<^bold>T \<bullet> \<^bold>T"
        using assms(1) and closed_wff_is_meaningful_regardless_of_assignment by metis
      also from assms and \<open>\<lambda>\<yy>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> have "
        \<V> ?\<phi>' ?g_witness \<bullet> \<^bold>T \<bullet> \<^bold>T = \<V> (?\<phi>'((\<xx>, o) := \<^bold>T)) (\<lambda>\<yy>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<bullet> \<^bold>T"
        using mixed_beta_conversion and truth_values_domain_def by auto
      also from assms(1) and \<open>\<lambda>\<yy>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> and is_assg_1 and calculation have "
        \<dots> = \<V> (?\<phi>'((\<xx>, o) := \<^bold>T, (\<yy>, o) := \<^bold>T)) (\<xx>\<^bsub>o\<^esub>)"
        using mixed_beta_conversion and is_assignment_def
        by (metis fun_upd_same fun_upd_twist fun_upd_upd wffs_of_type_intros(1))
      also have "\<dots> = \<^bold>T"
        using is_assg_2 and \<V>_is_wff_denotation_function by fastforce
      finally have "\<V> \<phi> ?g_witness \<bullet> \<^bold>T \<bullet> \<^bold>T = \<^bold>T" .
      with b have "\<V> \<phi> ?g_witness \<bullet> \<^bold>T \<bullet> \<^bold>T \<noteq> x"
        by blast
      moreover have "x = \<V> \<phi> ?g_witness \<bullet> x \<bullet> y"
      proof -
        from is_assg_\<phi>' have "x = \<V> ?\<phi>' (\<xx>\<^bsub>o\<^esub>)"
          using \<V>_is_wff_denotation_function by auto
        also from assms(2) and is_assg_\<phi>' have "\<dots> = \<V> ?\<phi>' (\<lambda>\<yy>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>) \<bullet> y"
          using wffs_of_type_intros(1)[where x = \<xx> and \<alpha> = o]
          by (simp add: mixed_beta_conversion \<V>_is_wff_denotation_function)
        also from assms(2) have "\<dots> = \<V> ?\<phi>' ?g_witness \<bullet> x \<bullet> y"
          using is_assg_\<phi>' and \<open>\<lambda>\<yy>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close>
          by (simp add: mixed_beta_conversion fun_upd_twist)
        also from assms(1,2) have "\<dots> = \<V> \<phi> ?g_witness \<bullet> x \<bullet> y"
          using is_assg_\<phi>' and \<open>is_closed_wff_of_type ?g_witness (o\<rightarrow>o\<rightarrow>o)\<close>
          and closed_wff_is_meaningful_regardless_of_assignment by metis
        finally show ?thesis .
      qed
      moreover from assms(1,2) have "\<V> \<phi> ?g_witness \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o))"
        using \<open>is_closed_wff_of_type ?g_witness (o\<rightarrow>o\<rightarrow>o)\<close> and \<V>_is_wff_denotation_function by simp
      ultimately have "\<exists>g \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o)). g \<bullet> \<^bold>T \<bullet> \<^bold>T \<noteq> g \<bullet> x \<bullet> y"
        by auto
      moreover from assms have "\<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y \<in> elts (\<D> o)"
        by (rule fully_applied_conj_fun_is_domain_respecting)
      ultimately have "\<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y = \<^bold>F"
        using and_eqv and truth_values_domain_def by fastforce
      with b show ?thesis
        by simp
    next
      case c
      let ?g_witness = "\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. \<yy>\<^bsub>o\<^esub>"
      have "\<lambda>\<yy>\<^bsub>o\<^esub>. \<yy>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
        by blast
      then have "is_closed_wff_of_type ?g_witness (o\<rightarrow>o\<rightarrow>o)"
        by force
      moreover from assms(1,2) have is_assg_\<phi>': "?\<phi>' \<leadsto> \<D>"
        by simp
      ultimately have "\<V> \<phi> ?g_witness \<bullet> \<^bold>T \<bullet> \<^bold>T = \<V> ?\<phi>' ?g_witness \<bullet> \<^bold>T \<bullet> \<^bold>T"
        using assms(1) and closed_wff_is_meaningful_regardless_of_assignment by metis
      also from is_assg_1 and is_assg_\<phi>' have "\<dots> = \<V> (?\<phi>'((\<xx>, o) := \<^bold>T)) (\<lambda>\<yy>\<^bsub>o\<^esub>. \<yy>\<^bsub>o\<^esub>) \<bullet> \<^bold>T"
        using \<open>\<lambda>\<yy>\<^bsub>o\<^esub>. \<yy>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> and mixed_beta_conversion and truth_values_domain_def by auto
      also from assms(1) and \<open>\<lambda>\<yy>\<^bsub>o\<^esub>. \<yy>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> and is_assg_1 and calculation have "
        \<dots> = \<V> (?\<phi>'((\<xx>, o) := \<^bold>T, (\<yy>, o) := \<^bold>T)) (\<yy>\<^bsub>o\<^esub>)"
        using mixed_beta_conversion and is_assignment_def
        by (metis fun_upd_same fun_upd_twist fun_upd_upd wffs_of_type_intros(1))
      also have "\<dots> = \<^bold>T"
        using is_assg_2 and \<V>_is_wff_denotation_function by force
      finally have "\<V> \<phi> ?g_witness \<bullet> \<^bold>T \<bullet> \<^bold>T = \<^bold>T" .
      with c have "\<V> \<phi> ?g_witness \<bullet> \<^bold>T \<bullet> \<^bold>T \<noteq> y"
        by blast
      moreover have "y = \<V> \<phi> ?g_witness \<bullet> x \<bullet> y"
      proof -
        from assms(2) and is_assg_\<phi>' have "y = \<V> ?\<phi>' (\<lambda>\<yy>\<^bsub>o\<^esub>. \<yy>\<^bsub>o\<^esub>) \<bullet> y"
          using wffs_of_type_intros(1)[where x = \<yy> and \<alpha> = o]
          and \<V>_is_wff_denotation_function and mixed_beta_conversion by auto
        also from assms(2) and \<open>\<lambda>\<yy>\<^bsub>o\<^esub>. \<yy>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> have "\<dots> = \<V> ?\<phi>' ?g_witness \<bullet> x \<bullet> y"
          using is_assg_\<phi>' by (simp add: mixed_beta_conversion fun_upd_twist)
        also from assms(1,2) have "\<dots> = \<V> \<phi> ?g_witness \<bullet> x \<bullet> y"
          using is_assg_\<phi>' and \<open>is_closed_wff_of_type ?g_witness (o\<rightarrow>o\<rightarrow>o)\<close>
          and closed_wff_is_meaningful_regardless_of_assignment by metis
        finally show ?thesis .
      qed
      moreover from assms(1) have "\<V> \<phi> ?g_witness \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o))"
        using \<open>is_closed_wff_of_type ?g_witness (o\<rightarrow>o\<rightarrow>o)\<close> and \<V>_is_wff_denotation_function by auto
      ultimately have "\<exists>g \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o)). g \<bullet> \<^bold>T \<bullet> \<^bold>T \<noteq> g \<bullet> x \<bullet> y"
        by auto
      moreover from assms have "\<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y \<in> elts (\<D> o)"
        by (rule fully_applied_conj_fun_is_domain_respecting)
      ultimately have "\<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y = \<^bold>F"
        using and_eqv and truth_values_domain_def by fastforce
      with c show ?thesis
        by simp
    qed
  qed
qed

corollary (in general_model) prop_5401_e':
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "\<V> \<phi> (A \<and>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<and> \<V> \<phi> B"
proof -
  from assms have "{\<V> \<phi> A, \<V> \<phi> B} \<subseteq> elts (\<D> o)"
    using \<V>_is_wff_denotation_function by simp
  from assms(2) have "\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by blast
  have "\<V> \<phi> (A \<and>\<^sup>\<Q> B) = \<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B)"
    by simp
  also from assms have "\<dots> = \<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A) \<bullet> \<V> \<phi> B"
    using \<V>_is_wff_denotation_function and \<open>\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> by blast
  also from assms have "\<dots> = \<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> \<V> \<phi> A \<bullet> \<V> \<phi> B"
    using \<V>_is_wff_denotation_function and conj_fun_wff by fastforce
  also from assms(1,2) have "\<dots> = (if \<V> \<phi> A = \<^bold>T \<and> \<V> \<phi> B = \<^bold>T then \<^bold>T else \<^bold>F)"
    using \<open>{\<V> \<phi> A, \<V> \<phi> B} \<subseteq> elts (\<D> o)\<close> and prop_5401_e by simp
  also have "\<dots> = \<V> \<phi> A \<^bold>\<and> \<V> \<phi> B"
    using truth_values_domain_def and \<open>{\<V> \<phi> A, \<V> \<phi> B} \<subseteq> elts (\<D> o)\<close> by fastforce
  finally show ?thesis .
qed

lemma (in general_model) prop_5401_f:
  assumes "\<phi> \<leadsto> \<D>"
  and "{x, y} \<subseteq> elts (\<D> o)"
  shows "\<V> \<phi> (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y = (if x = \<^bold>T \<and> y = \<^bold>F then \<^bold>F else \<^bold>T)"
proof -
  let ?\<phi>' = "\<phi>((\<xx>, o) := x, (\<yy>, o) := y)"
  from assms(2) have "{x, y} \<subseteq> elts \<bool>"
    unfolding truth_values_domain_def .
  have "(\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<^esub>"
    by blast
  then have "\<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by blast
  from assms have is_assg_\<phi>': "?\<phi>' \<leadsto> \<D>"
    by simp
  from assms(1) have "\<V> ?\<phi>' (\<xx>\<^bsub>o\<^esub>) = x" and "\<V> ?\<phi>' (\<yy>\<^bsub>o\<^esub>) = y"
    using is_assg_\<phi>' and \<V>_is_wff_denotation_function by force+
  have "\<V> \<phi> (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y = \<V> \<phi> (\<lambda>\<xx>\<^bsub>o\<^esub>. \<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<bullet> x \<bullet> y"
    by simp
  also from assms have "\<dots> = \<V> (\<phi>((\<xx>, o) := x)) (\<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)) \<bullet> y"
    using \<open>\<lambda>\<yy>\<^bsub>o\<^esub>. (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> and mixed_beta_conversion by simp
  also from assms have "\<dots> = \<V> ?\<phi>' (\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)"
    using mixed_beta_conversion and \<open>(\<xx>\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) \<in> wffs\<^bsub>o\<^esub>\<close> by simp
  finally have "\<V> \<phi> (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y = \<^bold>T \<longleftrightarrow> \<V> ?\<phi>' (\<xx>\<^bsub>o\<^esub>) = \<V> ?\<phi>' (\<xx>\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>)"
    using prop_5401_b'[OF is_assg_\<phi>'] and conj_op_wff and wffs_of_type_intros(1) by simp
  also have "\<dots> \<longleftrightarrow> x = x \<^bold>\<and> y"
    unfolding prop_5401_e'[OF is_assg_\<phi>' wffs_of_type_intros(1) wffs_of_type_intros(1)]
    and \<open>\<V> ?\<phi>' (\<xx>\<^bsub>o\<^esub>) = x\<close> and \<open>\<V> ?\<phi>' (\<yy>\<^bsub>o\<^esub>) = y\<close> ..
  also have "\<dots> \<longleftrightarrow> x = (if x = \<^bold>T \<and> y = \<^bold>T then \<^bold>T else \<^bold>F)"
    using \<open>{x, y} \<subseteq> elts \<bool>\<close> by auto
  also have "\<dots> \<longleftrightarrow> \<^bold>T = (if x = \<^bold>T \<and> y = \<^bold>F then \<^bold>F else \<^bold>T)"
    using \<open>{x, y} \<subseteq> elts \<bool>\<close> by auto
  finally show ?thesis
    using assms and fully_applied_imp_fun_denotation_is_domain_respecting and tv_cases
    and truth_values_domain_def by metis
qed

corollary (in general_model) prop_5401_f':
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "\<V> \<phi> (A \<supset>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<supset> \<V> \<phi> B"
proof -
  from assms have "{\<V> \<phi> A, \<V> \<phi> B} \<subseteq> elts (\<D> o)"
    using \<V>_is_wff_denotation_function by simp
  from assms(2) have "\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>"
    by blast
  have "\<V> \<phi> (A \<supset>\<^sup>\<Q> B) = \<V> \<phi> (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<sqdot> B)"
    by simp
  also from assms(1,3) have "\<dots> = \<V> \<phi> (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A) \<bullet> \<V> \<phi> B"
    using \<V>_is_wff_denotation_function and \<open>\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub> \<sqdot> A \<in> wffs\<^bsub>o\<rightarrow>o\<^esub>\<close> by blast
  also from assms have "\<dots> = \<V> \<phi> (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> \<V> \<phi> A \<bullet> \<V> \<phi> B"
    using \<V>_is_wff_denotation_function and imp_fun_wff by fastforce
  also from assms have "\<dots> = (if \<V> \<phi> A = \<^bold>T \<and> \<V> \<phi> B = \<^bold>F then \<^bold>F else \<^bold>T)"
    using \<open>{\<V> \<phi> A, \<V> \<phi> B} \<subseteq> elts (\<D> o)\<close> and prop_5401_f by simp
  also have "\<dots> = \<V> \<phi> A \<^bold>\<supset> \<V> \<phi> B"
    using truth_values_domain_def and \<open>{\<V> \<phi> A, \<V> \<phi> B} \<subseteq> elts (\<D> o)\<close> by auto
  finally show ?thesis .
qed

lemma (in general_model) forall_denotation:
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<V> \<phi> (\<forall>x\<^bsub>\<alpha>\<^esub>. A) = \<^bold>T \<longleftrightarrow> (\<forall>z \<in> elts (\<D> \<alpha>). \<V> (\<phi>((x, \<alpha>) := z)) A = \<^bold>T)"
proof -
  from assms(1) have lhs: "\<V> \<phi> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) \<bullet> z = \<^bold>T" if "z \<in> elts (\<D> \<alpha>)" for z
    using prop_5401_c and mixed_beta_conversion and that and true_wff by simp
  from assms have rhs: "\<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) \<bullet> z = \<V> (\<phi>((x, \<alpha>) := z)) A" if "z \<in> elts (\<D> \<alpha>)" for z
    using that by (simp add: mixed_beta_conversion)
  from assms(2) have "\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub> \<in> wffs\<^bsub>\<alpha>\<rightarrow>o\<^esub>" and "\<lambda>x\<^bsub>\<alpha>\<^esub>. A \<in> wffs\<^bsub>\<alpha>\<rightarrow>o\<^esub>"
    by auto
  have "\<V> \<phi> (\<forall>x\<^bsub>\<alpha>\<^esub>. A) = \<V> \<phi> (\<Prod>\<^bsub>\<alpha>\<^esub> \<sqdot> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A))"
    unfolding forall_def ..
  also have "\<dots> = \<V> \<phi> (Q\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) \<sqdot> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A))"
    unfolding PI_def ..
  also have "\<dots> = \<V> \<phi> ((\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>\<alpha>\<rightarrow>o\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A))"
    unfolding equality_of_type_def ..
  finally have "\<V> \<phi> (\<forall>x\<^bsub>\<alpha>\<^esub>. A) = \<V> \<phi> ((\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>\<alpha>\<rightarrow>o\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A))" .
  moreover from assms(1,2) have "
    \<V> \<phi> ((\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) =\<^bsub>\<alpha>\<rightarrow>o\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)) = \<^bold>T \<longleftrightarrow> \<V> \<phi> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) = \<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
    using \<open>\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub> \<in> wffs\<^bsub>\<alpha>\<rightarrow>o\<^esub>\<close> and \<open>\<lambda>x\<^bsub>\<alpha>\<^esub>. A \<in> wffs\<^bsub>\<alpha>\<rightarrow>o\<^esub>\<close> and prop_5401_b by blast
  moreover
  have "(\<V> \<phi> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) = \<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)) \<longleftrightarrow> (\<forall>z \<in> elts (\<D> \<alpha>). \<V> (\<phi>((x, \<alpha>) := z)) A = \<^bold>T)"
  proof
    assume "\<V> \<phi> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) = \<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
    with lhs and rhs show "\<forall>z \<in> elts (\<D> \<alpha>). \<V> (\<phi>((x, \<alpha>) := z)) A = \<^bold>T"
      by auto
  next
    assume "\<forall>z \<in> elts (\<D> \<alpha>). \<V> (\<phi>((x, \<alpha>) := z)) A = \<^bold>T"
    moreover from assms have "\<V> \<phi> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) = (\<^bold>\<lambda>z \<^bold>: \<D> \<alpha>\<^bold>. \<V> (\<phi>((\<xx>, \<alpha>) := z)) T\<^bsub>o\<^esub>)"
      using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by blast
    moreover from assms have "\<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = (\<^bold>\<lambda>z \<^bold>: \<D> \<alpha>\<^bold>. \<V> (\<phi>((x, \<alpha>) := z)) A)"
      using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by blast
    ultimately show "\<V> \<phi> (\<lambda>\<xx>\<^bsub>\<alpha>\<^esub>. T\<^bsub>o\<^esub>) = \<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
      using lhs and vlambda_extensionality by fastforce
  qed
  ultimately show ?thesis
    by (simp only:)
qed

lemma prop_5401_g:
  assumes "is_general_model \<M>"
  and "\<phi> \<leadsto>\<^sub>M \<M>"
  and "A \<in> wffs\<^bsub>o\<^esub>"
  shows "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> \<forall>x\<^bsub>\<alpha>\<^esub>. A \<longleftrightarrow> (\<forall>\<psi>. \<psi> \<leadsto>\<^sub>M \<M> \<and> \<psi> \<sim>\<^bsub>(x, \<alpha>)\<^esub> \<phi> \<longrightarrow> \<M> \<Turnstile>\<^bsub>\<psi>\<^esub> A)"
proof -
  obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
    using prod_cases3 by blast
  with assms have "
    \<M> \<Turnstile>\<^bsub>\<phi>\<^esub> \<forall>x\<^bsub>\<alpha>\<^esub>. A
    \<longleftrightarrow>
    \<forall>x\<^bsub>\<alpha>\<^esub>. A \<in> wffs\<^bsub>o\<^esub> \<and> is_general_model (\<D>, \<J>, \<V>) \<and> \<phi> \<leadsto> \<D> \<and> \<V> \<phi> (\<forall>x\<^bsub>\<alpha>\<^esub>. A) = \<^bold>T"
    by fastforce
  also from assms and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<dots> \<longleftrightarrow> (\<forall>z \<in> elts (\<D> \<alpha>). \<V> (\<phi>((x, \<alpha>) := z)) A = \<^bold>T)"
    using general_model.forall_denotation by fastforce
  also have "\<dots> \<longleftrightarrow> (\<forall>\<psi>. \<psi> \<leadsto> \<D> \<and> \<psi> \<sim>\<^bsub>(x, \<alpha>)\<^esub> \<phi> \<longrightarrow> \<M> \<Turnstile>\<^bsub>\<psi>\<^esub> A)"
  proof
    assume *: "\<forall>z \<in> elts (\<D> \<alpha>). \<V> (\<phi>((x, \<alpha>) := z)) A = \<^bold>T"
    {
      fix \<psi>
      assume "\<psi> \<leadsto> \<D>" and "\<psi> \<sim>\<^bsub>(x, \<alpha>)\<^esub> \<phi>"
      have "\<V> \<psi> A = \<^bold>T"
      proof -
        have "\<exists>z \<in> elts (\<D> \<alpha>). \<psi> = \<phi>((x, \<alpha>) := z)"
        proof (rule ccontr)
          assume "\<not> (\<exists>z \<in> elts (\<D> \<alpha>). \<psi> = \<phi>((x, \<alpha>) := z))"
          with \<open>\<psi> \<sim>\<^bsub>(x, \<alpha>)\<^esub> \<phi>\<close> have "\<forall>z \<in> elts (\<D> \<alpha>). \<psi> (x, \<alpha>) \<noteq> z"
            by fastforce
          then have "\<psi> (x, \<alpha>) \<notin> elts (\<D> \<alpha>)"
            by blast
          moreover from assms(1) and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and \<open>\<psi> \<leadsto> \<D>\<close> have "\<psi> (x, \<alpha>) \<in> elts (\<D> \<alpha>)"
            using general_model_def and premodel_def and frame.is_assignment_def by auto
          ultimately show False
            by simp
        qed
        with * show ?thesis
          by fastforce
      qed
      with assms(1) and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<M> \<Turnstile>\<^bsub>\<psi>\<^esub> A"
        by simp
    }
    then show "\<forall>\<psi>. \<psi> \<leadsto> \<D> \<and> \<psi> \<sim>\<^bsub>(x, \<alpha>)\<^esub> \<phi> \<longrightarrow> \<M> \<Turnstile>\<^bsub>\<psi>\<^esub> A"
      by blast
  next
    assume *: "\<forall>\<psi>. \<psi> \<leadsto> \<D> \<and> \<psi> \<sim>\<^bsub>(x, \<alpha>)\<^esub> \<phi> \<longrightarrow> \<M> \<Turnstile>\<^bsub>\<psi>\<^esub> A"
    show "\<forall>z \<in> elts (\<D> \<alpha>). \<V> (\<phi>((x, \<alpha>) := z)) A = \<^bold>T"
    proof
      fix z
      assume "z \<in> elts (\<D> \<alpha>)"
      with assms(1,2) and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<phi>((x, \<alpha>) := z) \<leadsto> \<D>"
        using general_model_def and premodel_def and frame.is_assignment_def by auto
      moreover have "\<phi>((x, \<alpha>) := z) \<sim>\<^bsub>(x, \<alpha>)\<^esub> \<phi>"
        by simp
      ultimately have "\<M> \<Turnstile>\<^bsub>\<phi>((x, \<alpha>) := z)\<^esub> A"
        using * by blast
      with assms(1) and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and \<open>\<phi>((x, \<alpha>) := z) \<leadsto> \<D>\<close> show "\<V> (\<phi>((x, \<alpha>) := z)) A = \<^bold>T"
        by simp
    qed
  qed
  finally show ?thesis
    using \<open>\<M> = (\<D>, \<J>, \<V>)\<close>
    by simp
qed

lemma (in general_model) axiom_1_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  shows "\<V> \<phi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>) = \<^bold>T" (is "\<V> \<phi> (?A \<equiv>\<^sup>\<Q> ?B) = \<^bold>T")
proof -
  let ?\<M> = "(\<D>, \<J>, \<V>)"
  from assms have *: "is_general_model ?\<M>" "\<phi> \<leadsto>\<^sub>M ?\<M>"
    using general_model_axioms by blast+
  have "?A \<equiv>\<^sup>\<Q> ?B \<in> wffs\<^bsub>o\<^esub>"
    using axioms.axiom_1 and axioms_are_wffs_of_type_o by blast
  have lhs: "\<V> \<phi> ?A = \<phi> (\<gg>, o\<rightarrow>o) \<bullet> \<^bold>T \<^bold>\<and> \<phi> (\<gg>, o\<rightarrow>o) \<bullet> \<^bold>F"
  proof -
    have "\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>" and "\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
      by blast+
    with assms have "\<V> \<phi> ?A = \<V> \<phi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub>) \<^bold>\<and> \<V> \<phi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub>)"
      using prop_5401_e' by simp
    also from assms have "\<dots> = \<phi> (\<gg>, o\<rightarrow>o) \<bullet> \<V> \<phi> (T\<^bsub>o\<^esub>) \<^bold>\<and> \<phi> (\<gg>, o\<rightarrow>o) \<bullet> \<V> \<phi> (F\<^bsub>o\<^esub>)"
      using wff_app_denotation[OF \<V>_is_wff_denotation_function]
      and wff_var_denotation[OF \<V>_is_wff_denotation_function]
      by (metis false_wff true_wff wffs_of_type_intros(1))
    finally show ?thesis
      using assms and prop_5401_c and prop_5401_d by simp
  qed
  have "\<V> \<phi> (?A \<equiv>\<^sup>\<Q> ?B) = \<^bold>T"
  proof (cases "\<forall>z \<in> elts (\<D> o). \<phi> (\<gg>, o\<rightarrow>o) \<bullet> z = \<^bold>T")
    case True
    with assms have "\<phi> (\<gg>, o\<rightarrow>o) \<bullet> \<^bold>T = \<^bold>T" and "\<phi> (\<gg>, o\<rightarrow>o) \<bullet> \<^bold>F = \<^bold>T"
      using truth_values_domain_def by auto
    with lhs have "\<V> \<phi> ?A = \<^bold>T \<^bold>\<and> \<^bold>T"
      by (simp only:)
    also have "\<dots> = \<^bold>T"
      by simp
    finally have "\<V> \<phi> ?A = \<^bold>T" .
    moreover have "\<V> \<phi> ?B = \<^bold>T"
    proof -
      have "\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>"
        by blast
      moreover
      {
        fix \<psi>
        assume "\<psi> \<leadsto> \<D>" and "\<psi> \<sim>\<^bsub>(\<xx>, o)\<^esub> \<phi>"
        with assms have "\<V> \<psi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>) = \<V> \<psi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub>) \<bullet> \<V> \<psi> (\<xx>\<^bsub>o\<^esub>)"
          using \<V>_is_wff_denotation_function by blast
        also from \<open>\<psi> \<leadsto> \<D>\<close> have "\<dots> = \<psi> (\<gg>, o\<rightarrow>o) \<bullet> \<psi> (\<xx>, o)"
          using \<V>_is_wff_denotation_function by auto
        also from \<open>\<psi> \<sim>\<^bsub>(\<xx>, o)\<^esub> \<phi>\<close> have "\<dots> = \<phi> (\<gg>, o\<rightarrow>o) \<bullet> \<psi> (\<xx>, o)"
          by simp
        also from True and \<open>\<psi> \<leadsto> \<D>\<close> have "\<dots> = \<^bold>T"
          by blast
        finally have "\<V> \<psi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>) = \<^bold>T" .
        with assms and \<open>\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub> \<in> wffs\<^bsub>o\<^esub>\<close> have "?\<M> \<Turnstile>\<^bsub>\<psi>\<^esub> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>"
          by simp
      }
      ultimately have "?\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?B"
        using assms and * and prop_5401_g by auto
      with *(2) show ?thesis
        by simp
    qed
    ultimately show ?thesis
      using assms and prop_5401_b' and wffs_from_equivalence[OF \<open>?A \<equiv>\<^sup>\<Q> ?B \<in> wffs\<^bsub>o\<^esub>\<close>] by simp
  next
    case False
    then have "\<exists>z \<in> elts (\<D> o). \<phi> (\<gg>, o\<rightarrow>o) \<bullet> z \<noteq> \<^bold>T"
      by blast
    moreover from * have "\<forall>z \<in> elts (\<D> o). \<phi> (\<gg>, o\<rightarrow>o) \<bullet> z \<in> elts (\<D> o)"
      using app_is_domain_respecting by blast
    ultimately obtain z where "z \<in> elts (\<D> o)" and "\<phi> (\<gg>, o\<rightarrow>o) \<bullet> z = \<^bold>F"
      using truth_values_domain_def by auto
    define \<psi> where \<psi>_def: "\<psi> = \<phi>((\<xx>, o) := z)"
    with * and \<open>z \<in> elts (\<D> o)\<close> have "\<psi> \<leadsto> \<D>"
      by simp
    then have "\<V> \<psi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>) = \<V> \<psi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub>) \<bullet> \<V> \<psi> (\<xx>\<^bsub>o\<^esub>)"
      using \<V>_is_wff_denotation_function by blast
    also from \<open>\<psi> \<leadsto> \<D>\<close> have "\<dots> = \<psi> (\<gg>, o\<rightarrow>o) \<bullet> \<psi> (\<xx>, o)"
      using \<V>_is_wff_denotation_function by auto
    also from \<psi>_def have "\<dots> = \<phi> (\<gg>, o\<rightarrow>o) \<bullet> z"
      by simp
    also have "\<dots> = \<^bold>F"
      unfolding \<open>\<phi> (\<gg>, o\<rightarrow>o) \<bullet> z = \<^bold>F\<close> ..
    finally have "\<V> \<psi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>) = \<^bold>F" .
    with \<open>\<psi> \<leadsto> \<D>\<close> have "\<not> ?\<M> \<Turnstile>\<^bsub>\<psi>\<^esub> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>"
      by (auto simp add: inj_eq)
    with \<open>\<psi> \<leadsto> \<D>\<close> and \<psi>_def have "\<not> (\<forall>\<psi>. \<psi> \<leadsto> \<D> \<and> \<psi> \<sim>\<^bsub>(\<xx>, o)\<^esub> \<phi> \<longrightarrow> ?\<M> \<Turnstile>\<^bsub>\<psi>\<^esub> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>)"
      using fun_upd_other by fastforce
    with \<open>\<not> ?\<M> \<Turnstile>\<^bsub>\<psi>\<^esub> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>\<close> have "\<not> ?\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?B"
      using prop_5401_g[OF * wffs_from_forall[OF wffs_from_equivalence(2)[OF \<open>?A \<equiv>\<^sup>\<Q> ?B \<in> wffs\<^bsub>o\<^esub>\<close>]]]
      by blast
    then have "\<V> \<phi> (\<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>) \<noteq> \<^bold>T"
      by simp
    moreover from assms have "\<V> \<phi> ?B \<in> elts (\<D> o)"
      using wffs_from_equivalence[OF \<open>?A \<equiv>\<^sup>\<Q> ?B \<in> wffs\<^bsub>o\<^esub>\<close>] and \<V>_is_wff_denotation_function by auto
    ultimately have "\<V> \<phi> ?B = \<^bold>F"
      by (simp add: truth_values_domain_def)
    moreover have "\<V> \<phi> (\<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub>) = \<^bold>F"
    proof -
      from \<open>z \<in> elts (\<D> o)\<close> and \<open>\<phi> (\<gg>, o\<rightarrow>o) \<bullet> z = \<^bold>F\<close>
      have "((\<phi> (\<gg>, o\<rightarrow>o)) \<bullet> \<^bold>T) = \<^bold>F \<or> ((\<phi> (\<gg>, o\<rightarrow>o)) \<bullet> \<^bold>F) = \<^bold>F"
        using truth_values_domain_def by fastforce
      moreover from \<open>z \<in> elts (\<D> o)\<close> and \<open>\<phi> (\<gg>, o\<rightarrow>o) \<bullet> z = \<^bold>F\<close>
        and \<open>\<forall>z \<in> elts (\<D> o). \<phi> (\<gg>, o\<rightarrow>o) \<bullet> z \<in> elts (\<D> o)\<close>
      have "{(\<phi> (\<gg>, o\<rightarrow>o)) \<bullet> \<^bold>T, (\<phi> (\<gg>, o\<rightarrow>o)) \<bullet> \<^bold>F} \<subseteq> elts (\<D> o)"
        by (simp add: truth_values_domain_def)
      ultimately have "((\<phi> (\<gg>, o\<rightarrow>o)) \<bullet> \<^bold>T) \<^bold>\<and> ((\<phi> (\<gg>, o\<rightarrow>o)) \<bullet> \<^bold>F) = \<^bold>F"
        by auto
      with lhs show ?thesis
        by (simp only:)
    qed
    ultimately show ?thesis
      using assms and prop_5401_b' and wffs_from_equivalence[OF \<open>?A \<equiv>\<^sup>\<Q> ?B \<in> wffs\<^bsub>o\<^esub>\<close>] by simp
  qed
  then show ?thesis .
qed

lemma axiom_1_validity:
  shows "\<Turnstile> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> T\<^bsub>o\<^esub> \<and>\<^sup>\<Q> \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> \<forall>\<xx>\<^bsub>o\<^esub>. \<gg>\<^bsub>o\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>o\<^esub>" (is "\<Turnstile> ?A \<equiv>\<^sup>\<Q> ?B")
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?A \<equiv>\<^sup>\<Q> ?B"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover from * and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> (?A \<equiv>\<^sup>\<Q> ?B) = \<^bold>T"
      using general_model.axiom_1_validity_aux by simp
    ultimately show ?thesis
      by simp
  qed
qed

lemma (in general_model) axiom_2_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  shows "\<V> \<phi> ((\<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<alpha>\<^esub> \<yy>\<^bsub>\<alpha>\<^esub>) \<supset>\<^sup>\<Q> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> \<equiv>\<^sup>\<Q> \<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>)) = \<^bold>T" (is "\<V> \<phi> (?A \<supset>\<^sup>\<Q> ?B) = \<^bold>T")
proof -
  have "?A \<supset>\<^sup>\<Q> ?B \<in> wffs\<^bsub>o\<^esub>"
    using axioms.axiom_2 and axioms_are_wffs_of_type_o by blast
  from \<open>?A \<supset>\<^sup>\<Q> ?B \<in> wffs\<^bsub>o\<^esub>\<close> have "?A \<in> wffs\<^bsub>o\<^esub>" and "?B \<in> wffs\<^bsub>o\<^esub>"
    using wffs_from_imp_op by blast+
  with assms have "\<V> \<phi> (?A \<supset>\<^sup>\<Q> ?B) = \<V> \<phi> ?A \<^bold>\<supset> \<V> \<phi> ?B"
    using prop_5401_f' by simp
  moreover from assms and \<open>?A \<in> wffs\<^bsub>o\<^esub>\<close> and \<open>?B \<in> wffs\<^bsub>o\<^esub>\<close> have "{\<V> \<phi> ?A, \<V> \<phi> ?B} \<subseteq> elts (\<D> o)"
    using \<V>_is_wff_denotation_function by simp
  then have "{\<V> \<phi> ?A, \<V> \<phi> ?B} \<subseteq> elts \<bool>"
    by (simp add: truth_values_domain_def)
  ultimately have \<V>_imp_T: "\<V> \<phi> (?A \<supset>\<^sup>\<Q> ?B) = \<^bold>T \<longleftrightarrow> \<V> \<phi> ?A = \<^bold>F \<or> \<V> \<phi> ?B = \<^bold>T"
    by fastforce
  then show ?thesis
  proof (cases "\<phi> (\<xx>, \<alpha>) = \<phi> (\<yy>, \<alpha>)")
    case True
    from assms and \<open>?B \<in> wffs\<^bsub>o\<^esub>\<close> have "\<V> \<phi> ?B = \<^bold>T \<longleftrightarrow> \<V> \<phi> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<V> \<phi> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>)"
      using wffs_from_equivalence and prop_5401_b' by metis
    moreover have "\<V> \<phi> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<V> \<phi> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>)"
    proof -
      from assms and \<open>?B \<in> wffs\<^bsub>o\<^esub>\<close> have "\<V> \<phi> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<V> \<phi> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub>) \<bullet> \<V> \<phi> (\<xx>\<^bsub>\<alpha>\<^esub>)"
        using \<V>_is_wff_denotation_function by blast
      also from assms have "\<dots> = \<phi> (\<hh>, \<alpha>\<rightarrow>o) \<bullet> \<phi> (\<xx>, \<alpha>)"
        using \<V>_is_wff_denotation_function by auto
      also from True have "\<dots> = \<phi> (\<hh>, \<alpha>\<rightarrow>o) \<bullet> \<phi> (\<yy>, \<alpha>)"
        by (simp only:)
      also from assms have "\<dots> = \<V> \<phi> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub>) \<bullet> \<V> \<phi> (\<yy>\<^bsub>\<alpha>\<^esub>)"
        using \<V>_is_wff_denotation_function by auto
      also from assms and \<open>?B \<in> wffs\<^bsub>o\<^esub>\<close> have "\<dots> = \<V> \<phi> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>)"
        using wff_app_denotation[OF \<V>_is_wff_denotation_function] by (metis wffs_of_type_intros(1))
      finally show ?thesis .
    qed
    ultimately show ?thesis
      using \<V>_imp_T by simp
  next
    case False
    from assms have "\<V> \<phi> ?A = \<^bold>T \<longleftrightarrow> \<V> \<phi> (\<xx>\<^bsub>\<alpha>\<^esub>) = \<V> \<phi> (\<yy>\<^bsub>\<alpha>\<^esub>)"
      using prop_5401_b by blast
    moreover from False and assms have "\<V> \<phi> (\<xx>\<^bsub>\<alpha>\<^esub>) \<noteq> \<V> \<phi> (\<yy>\<^bsub>\<alpha>\<^esub>)"
      using \<V>_is_wff_denotation_function by auto
    ultimately have "\<V> \<phi> ?A = \<^bold>F"
      using assms and \<open>{\<V> \<phi> ?A, \<V> \<phi> ?B} \<subseteq> elts \<bool>\<close> by simp
    then show ?thesis
      using \<V>_imp_T by simp
  qed
qed

lemma axiom_2_validity:
  shows "\<Turnstile> (\<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<alpha>\<^esub> \<yy>\<^bsub>\<alpha>\<^esub>) \<supset>\<^sup>\<Q> (\<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> \<equiv>\<^sup>\<Q> \<hh>\<^bsub>\<alpha>\<rightarrow>o\<^esub> \<sqdot> \<yy>\<^bsub>\<alpha>\<^esub>)" (is "\<Turnstile> ?A \<supset>\<^sup>\<Q> ?B")
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?A \<supset>\<^sup>\<Q> ?B"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover from * and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> (?A \<supset>\<^sup>\<Q> ?B) = \<^bold>T"
      using general_model.axiom_2_validity_aux by simp
    ultimately show ?thesis
      by force
  qed
qed

lemma (in general_model) axiom_3_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  shows "\<V> \<phi> ((\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) \<equiv>\<^sup>\<Q> \<forall>\<xx>\<^bsub>\<alpha>\<^esub>. (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)) = \<^bold>T"
  (is "\<V> \<phi> (?A \<equiv>\<^sup>\<Q> ?B) = \<^bold>T")
proof -
  let ?\<M> = "(\<D>, \<J>, \<V>)"
  from assms have *: "is_general_model ?\<M>" "\<phi> \<leadsto>\<^sub>M ?\<M>"
    using general_model_axioms by blast+
  have B'_wffo: "\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> \<in> wffs\<^bsub>o\<^esub>"
    by blast
  have "?A \<equiv>\<^sup>\<Q> ?B \<in> wffs\<^bsub>o\<^esub>" and "?A \<in> wffs\<^bsub>o\<^esub>" and "?B \<in> wffs\<^bsub>o\<^esub>"
  proof -
    show "?A \<equiv>\<^sup>\<Q> ?B \<in> wffs\<^bsub>o\<^esub>"
      using axioms.axiom_3 and axioms_are_wffs_of_type_o
      by blast
    then show "?A \<in> wffs\<^bsub>o\<^esub>" and "?B \<in> wffs\<^bsub>o\<^esub>"
      by (blast dest: wffs_from_equivalence)+
  qed
  have "\<V> \<phi> ?A = \<V> \<phi> ?B"
  proof (cases "\<phi> (\<ff>, \<alpha>\<rightarrow>\<beta>) = \<phi> (\<gg>, \<alpha>\<rightarrow>\<beta>)")
    case True
    have "\<V> \<phi> ?A = \<^bold>T"
    proof -
      from assms have "\<V> \<phi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) = \<phi> (\<ff>, \<alpha>\<rightarrow>\<beta>)"
        using \<V>_is_wff_denotation_function by auto
      also from True have "\<dots> = \<phi> (\<gg>, \<alpha>\<rightarrow>\<beta>)"
        by (simp only:)
      also from assms have "\<dots> = \<V> \<phi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>)"
        using \<V>_is_wff_denotation_function by auto
      finally have "\<V> \<phi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) = \<V> \<phi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>)" .
      with assms show ?thesis
        using prop_5401_b by blast
    qed
    moreover have "\<V> \<phi> ?B = \<^bold>T"
    proof -
      {
        fix \<psi>
        assume "\<psi> \<leadsto> \<D>" and "\<psi> \<sim>\<^bsub>(\<xx>, \<alpha>)\<^esub> \<phi>"
        from assms and \<open>\<psi> \<leadsto> \<D>\<close> have "\<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) \<bullet> \<V> \<psi> (\<xx>\<^bsub>\<alpha>\<^esub>)"
          using \<V>_is_wff_denotation_function by blast
        also from assms and \<open>\<psi> \<leadsto> \<D>\<close> have "\<dots> = \<psi> (\<ff>, \<alpha>\<rightarrow>\<beta>) \<bullet> \<psi> (\<xx>, \<alpha>)"
          using \<V>_is_wff_denotation_function by auto
        also from \<open>\<psi> \<sim>\<^bsub>(\<xx>, \<alpha>)\<^esub> \<phi>\<close> have "\<dots> = \<phi> (\<ff>, \<alpha>\<rightarrow>\<beta>) \<bullet> \<psi> (\<xx>, \<alpha>)"
          by simp
        also from True have "\<dots> = \<phi> (\<gg>, \<alpha>\<rightarrow>\<beta>) \<bullet> \<psi> (\<xx>, \<alpha>)"
          by (simp only:)
        also from \<open>\<psi> \<sim>\<^bsub>(\<xx>, \<alpha>)\<^esub> \<phi>\<close> have "\<dots> = \<psi> (\<gg>, \<alpha>\<rightarrow>\<beta>) \<bullet> \<psi> (\<xx>, \<alpha>)"
          by simp
        also from assms and \<open>\<psi> \<leadsto> \<D>\<close> have "\<dots> = \<V> \<psi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) \<bullet> \<V> \<psi> (\<xx>\<^bsub>\<alpha>\<^esub>)"
          using \<V>_is_wff_denotation_function by auto
        also from assms and \<open>\<psi> \<leadsto> \<D>\<close> have "\<dots> = \<V> \<psi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)"
          using wff_app_denotation[OF \<V>_is_wff_denotation_function] by (metis wffs_of_type_intros(1))
        finally have "\<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<V> \<psi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)" .
        with B'_wffo and assms and \<open>\<psi> \<leadsto> \<D>\<close> have "\<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<^bold>T"
          using prop_5401_b and wffs_from_equality by blast
        with *(2) have "?\<M> \<Turnstile>\<^bsub>\<psi>\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>"
          by simp
      }
      with * and B'_wffo have "?\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?B"
        using prop_5401_g by force
      with *(2) show ?thesis
        by auto
    qed
    ultimately show ?thesis ..
  next
    case False
    from * have "\<phi> (\<ff>, \<alpha>\<rightarrow>\<beta>) \<in> elts (\<D> \<alpha> \<longmapsto> \<D> \<beta>)" and "\<phi> (\<gg>, \<alpha>\<rightarrow>\<beta>) \<in> elts (\<D> \<alpha> \<longmapsto> \<D> \<beta>)"
      by (simp_all add: function_domainD)
    with False obtain z where "z \<in> elts (\<D> \<alpha>)" and "\<phi> (\<ff>, \<alpha>\<rightarrow>\<beta>) \<bullet> z \<noteq> \<phi> (\<gg>, \<alpha>\<rightarrow>\<beta>) \<bullet> z"
      by (blast dest: fun_ext)
    define \<psi> where "\<psi> = \<phi>((\<xx>, \<alpha>) := z)"
    from * and \<open>z \<in> elts (\<D> \<alpha>)\<close> have "\<psi> \<leadsto> \<D>" and "\<psi> \<sim>\<^bsub>(\<xx>, \<alpha>)\<^esub> \<phi>"
      unfolding \<psi>_def by fastforce+
    have "\<V> \<psi> (f\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<phi> (f, \<alpha>\<rightarrow>\<beta>) \<bullet> z" for f
    proof -
      from \<open>\<psi> \<leadsto> \<D>\<close> have "\<V> \<psi> (f\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<V> \<psi> (f\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) \<bullet> \<V> \<psi> (\<xx>\<^bsub>\<alpha>\<^esub>)"
        using \<V>_is_wff_denotation_function by blast
      also from \<open>\<psi> \<leadsto> \<D>\<close> have "\<dots> = \<psi> (f, \<alpha>\<rightarrow>\<beta>) \<bullet> \<psi> (\<xx>, \<alpha>)"
        using \<V>_is_wff_denotation_function by auto
      finally show ?thesis
        unfolding \<psi>_def by simp
    qed
    then have "\<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<phi> (\<ff>, \<alpha>\<rightarrow>\<beta>) \<bullet> z" and "\<V> \<psi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<phi> (\<gg>, \<alpha>\<rightarrow>\<beta>) \<bullet> z"
      by (simp_all only:)
    with \<open>\<phi> (\<ff>, \<alpha>\<rightarrow>\<beta>) \<bullet> z \<noteq> \<phi> (\<gg>, \<alpha>\<rightarrow>\<beta>) \<bullet> z\<close> have "\<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<noteq> \<V> \<psi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)"
      by simp
    then have "\<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) = \<^bold>F"
    proof -
      from B'_wffo and \<open>\<psi> \<leadsto> \<D>\<close> and * have "\<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<in> elts (\<D> o)"
        using \<V>_is_wff_denotation_function by auto
      moreover from B'_wffo have "{\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>, \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>} \<subseteq> wffs\<^bsub>\<beta>\<^esub>"
        by blast
      with \<open>\<psi> \<leadsto> \<D>\<close> and \<open>\<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<noteq> \<V> \<psi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)\<close> and B'_wffo
      have "\<V> \<psi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>) \<noteq> \<^bold>T"
        using prop_5401_b by simp
      ultimately show ?thesis
        by (simp add: truth_values_domain_def)
    qed
    with \<open>\<psi> \<leadsto> \<D>\<close> have "\<not> ?\<M> \<Turnstile>\<^bsub>\<psi>\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>"
      by (auto simp add: inj_eq)
    with \<open>\<psi> \<leadsto> \<D>\<close> and \<open>\<psi> \<sim>\<^bsub>(\<xx>, \<alpha>)\<^esub> \<phi>\<close>
    have "\<exists>\<psi>. \<psi> \<leadsto> \<D> \<and> \<psi> \<sim>\<^bsub>(\<xx>, \<alpha>)\<^esub> \<phi> \<and> \<not> ?\<M> \<Turnstile>\<^bsub>\<psi>\<^esub> \<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>"
      by blast
    with * and B'_wffo have "\<not> ?\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?B"
      using prop_5401_g by blast
    then have "\<V> \<phi> ?B = \<^bold>F"
    proof -
      from \<open>?B \<in> wffs\<^bsub>o\<^esub>\<close> and * have "\<V> \<phi> ?B \<in> elts (\<D> o)"
        using \<V>_is_wff_denotation_function by auto
      with \<open>\<not> ?\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?B\<close> and \<open>?B \<in> wffs\<^bsub>o\<^esub>\<close> show ?thesis
        using truth_values_domain_def by fastforce
    qed
    moreover have "\<V> \<phi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) = \<^bold>F"
    proof -
      from * have "\<V> \<phi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) = \<phi> (\<ff>, \<alpha>\<rightarrow>\<beta>)" and "\<V> \<phi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) = \<phi> (\<gg>, \<alpha>\<rightarrow>\<beta>)"
        using \<V>_is_wff_denotation_function by auto
      with False have "\<V> \<phi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) \<noteq> \<V> \<phi> (\<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>)"
        by simp
      with * have "\<V> \<phi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) \<noteq> \<^bold>T"
        using prop_5401_b by blast
      moreover from * and \<open>?A \<in> wffs\<^bsub>o\<^esub>\<close> have "\<V> \<phi> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) \<in> elts (\<D> o)"
        using \<V>_is_wff_denotation_function by auto
      ultimately show ?thesis
        by (simp add: truth_values_domain_def)
    qed
    ultimately show ?thesis
      by (simp only:)
  qed
  with * and \<open>?A \<in> wffs\<^bsub>o\<^esub>\<close> and \<open>?B \<in> wffs\<^bsub>o\<^esub>\<close> show ?thesis
    using prop_5401_b' by simp
qed

lemma axiom_3_validity:
  shows "\<Turnstile> (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> =\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub>) \<equiv>\<^sup>\<Q> \<forall>\<xx>\<^bsub>\<alpha>\<^esub>. (\<ff>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> \<gg>\<^bsub>\<alpha>\<rightarrow>\<beta>\<^esub> \<sqdot> \<xx>\<^bsub>\<alpha>\<^esub>)" (is "\<Turnstile> ?A \<equiv>\<^sup>\<Q> ?B")
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?A \<equiv>\<^sup>\<Q> ?B"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover from * and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> (?A \<equiv>\<^sup>\<Q> ?B) = \<^bold>T"
      using general_model.axiom_3_validity_aux by simp
    ultimately show ?thesis
      by simp
  qed
qed

lemma (in general_model) axiom_4_1_con_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) = \<^bold>T"
proof -
  from assms(2) have "(\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub> \<in> wffs\<^bsub>o\<^esub>"
    using axioms.axiom_4_1_con and axioms_are_wffs_of_type_o by blast
  define \<psi> where "\<psi> = \<phi>((x, \<alpha>) := \<V> \<phi> A)"
  from assms have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A) = \<V> (\<phi>((x, \<alpha>) := \<V> \<phi> A)) (\<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>)"
    using prop_5401_a by blast
  also have "\<dots> = \<V> \<psi> (\<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>)"
    unfolding \<psi>_def ..
  also from assms and \<psi>_def have "\<dots> = \<V> \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>)"
    using \<V>_is_wff_denotation_function by auto
  finally have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A) = \<V> \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>)" .
  with assms(1) and \<open>(\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub> \<in> wffs\<^bsub>o\<^esub>\<close> show ?thesis
    using wffs_from_equality(1) and prop_5401_b by blast
qed

lemma axiom_4_1_con_validity:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<Turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>"
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover from assms and * and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<lbrace>c\<rbrace>\<^bsub>\<beta>\<^esub>) = \<^bold>T"
      using general_model.axiom_4_1_con_validity_aux by simp
    ultimately show ?thesis
      by simp
  qed
qed

lemma (in general_model) axiom_4_1_var_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "(y, \<beta>) \<noteq> (x, \<alpha>)"
  shows "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> y\<^bsub>\<beta>\<^esub>) = \<^bold>T"
proof -
  from assms(2) have "(\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> y\<^bsub>\<beta>\<^esub> \<in> wffs\<^bsub>o\<^esub>"
    using axioms.axiom_4_1_var and axioms_are_wffs_of_type_o by blast
  define \<psi> where "\<psi> = \<phi>((x, \<alpha>) := \<V> \<phi> A)"
  with assms(1,2) have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A) = \<V> (\<phi>((x, \<alpha>) := \<V> \<phi> A)) (y\<^bsub>\<beta>\<^esub>)"
    using prop_5401_a by blast
  also have "\<dots> = \<V> \<psi> (y\<^bsub>\<beta>\<^esub>)"
    unfolding \<psi>_def ..
  also have "\<dots> = \<V> \<phi> (y\<^bsub>\<beta>\<^esub>)"
  proof -
    from assms(1,2) have "\<V> \<phi> A \<in> elts (\<D> \<alpha>)"
      using \<V>_is_wff_denotation_function by auto
    with \<psi>_def and assms(1) have "\<psi> \<leadsto> \<D>"
      by simp
    moreover have "free_vars (y\<^bsub>\<beta>\<^esub>) = {(y, \<beta>)}"
      by simp
    with \<psi>_def and assms(3) have "\<forall>v \<in> free_vars (y\<^bsub>\<beta>\<^esub>). \<phi> v = \<psi> v"
      by auto
    ultimately show ?thesis
      using prop_5400[OF wffs_of_type_intros(1) assms(1)] by simp
  qed
  finally have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A) = \<V> \<phi> (y\<^bsub>\<beta>\<^esub>)" .
  with \<open>(\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> y\<^bsub>\<beta>\<^esub> \<in> wffs\<^bsub>o\<^esub>\<close> show ?thesis
    using wffs_from_equality(1) and prop_5401_b[OF assms(1)] by blast
qed

lemma axiom_4_1_var_validity:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "(y, \<beta>) \<noteq> (x, \<alpha>)"
  shows "\<Turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> y\<^bsub>\<beta>\<^esub>"
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> y\<^bsub>\<beta>\<^esub>"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover from assms and * and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. y\<^bsub>\<beta>\<^esub>) \<sqdot> A =\<^bsub>\<beta>\<^esub> y\<^bsub>\<beta>\<^esub>) = \<^bold>T"
      using general_model.axiom_4_1_var_validity_aux by auto
    ultimately show ?thesis
      by simp
  qed
qed

lemma (in general_model) axiom_4_2_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A) = \<^bold>T"
proof -
  from assms(2) have "(\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A \<in> wffs\<^bsub>o\<^esub>"
    using axioms.axiom_4_2 and axioms_are_wffs_of_type_o by blast
  define \<psi> where "\<psi> = \<phi>((x, \<alpha>) := \<V> \<phi> A)"
  with assms have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A) = \<V> \<psi> (x\<^bsub>\<alpha>\<^esub>)"
    using prop_5401_a by blast
  also from assms and \<psi>_def have "\<dots> = \<psi> (x, \<alpha>)"
    using \<V>_is_wff_denotation_function by force
  also from \<psi>_def have "\<dots> = \<V> \<phi> A"
    by simp
  finally have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A) = \<V> \<phi> A" .
  with assms(1) and \<open>(\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A \<in> wffs\<^bsub>o\<^esub>\<close> show ?thesis
    using wffs_from_equality and prop_5401_b by meson
qed

lemma axiom_4_2_validity:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<Turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A"
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover from assms and * and  \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. x\<^bsub>\<alpha>\<^esub>) \<sqdot> A =\<^bsub>\<alpha>\<^esub> A) = \<^bold>T"
      using general_model.axiom_4_2_validity_aux by simp
    ultimately show ?thesis
      by simp
  qed
qed

lemma (in general_model) axiom_4_3_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>" and "C \<in> wffs\<^bsub>\<gamma>\<^esub>"
  shows "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B \<sqdot> C) \<sqdot> A =\<^bsub>\<beta>\<^esub> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) \<sqdot> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A)) = \<^bold>T"
  (is "\<V> \<phi> (?A =\<^bsub>\<beta>\<^esub> ?B) = \<^bold>T")
proof -
  from assms(2-4) have "?A =\<^bsub>\<beta>\<^esub> ?B \<in> wffs\<^bsub>o\<^esub>"
    using axioms.axiom_4_3 and axioms_are_wffs_of_type_o by blast
  define \<psi> where "\<psi> = \<phi>((x, \<alpha>) := \<V> \<phi> A)"
  with assms(1,2) have "\<psi> \<leadsto> \<D>"
    using \<V>_is_wff_denotation_function by auto
  from assms and \<psi>_def have "\<V> \<phi> ?A = \<V> \<psi> (B \<sqdot> C)"
    using prop_5401_a by blast
  also from assms(3,4) and \<psi>_def and \<open>\<psi> \<leadsto> \<D>\<close> have "\<dots> = \<V> \<psi> B \<bullet> \<V> \<psi> C"
    using \<V>_is_wff_denotation_function by blast
  also from assms(1-3) and \<psi>_def have "\<dots> = \<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) \<bullet> \<V> \<psi> C"
    using prop_5401_a by simp
  also from assms(1,2,4) and \<psi>_def have "\<dots> = \<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) \<bullet> \<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A)"
    using prop_5401_a by simp
  also have "\<dots> = \<V> \<phi> ?B"
  proof -
    have "(\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>" and "(\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A \<in> wffs\<^bsub>\<gamma>\<^esub>"
      using assms(2-4) by blast+
    with assms(1) show ?thesis
      using wff_app_denotation[OF \<V>_is_wff_denotation_function] by simp
  qed
  finally have "\<V> \<phi> ?A = \<V> \<phi> ?B" .
  with assms(1) and \<open>?A =\<^bsub>\<beta>\<^esub> ?B \<in> wffs\<^bsub>o\<^esub>\<close> show ?thesis
    using prop_5401_b and wffs_from_equality by meson
qed

lemma axiom_4_3_validity:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>" and "C \<in> wffs\<^bsub>\<gamma>\<^esub>"
  shows "\<Turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B \<sqdot> C) \<sqdot> A =\<^bsub>\<beta>\<^esub> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) \<sqdot> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. C) \<sqdot> A)" (is "\<Turnstile> ?A =\<^bsub>\<beta>\<^esub> ?B")
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?A =\<^bsub>\<beta>\<^esub> ?B"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover from assms and * and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> (?A =\<^bsub>\<beta>\<^esub> ?B) = \<^bold>T"
      using general_model.axiom_4_3_validity_aux by simp
    ultimately show ?thesis
      by simp
  qed
qed

lemma (in general_model) axiom_4_4_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<delta>\<^esub>"
  and "(y, \<gamma>) \<notin> {(x, \<alpha>)} \<union> vars A"
  shows "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. B) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> (\<lambda>y\<^bsub>\<gamma>\<^esub>. (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A)) = \<^bold>T"
  (is "\<V> \<phi> (?A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> ?B) = \<^bold>T")
proof -
  from assms(2,3) have "?A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> ?B \<in> wffs\<^bsub>o\<^esub>"
    using axioms.axiom_4_4 and axioms_are_wffs_of_type_o by blast
  let ?D = "\<lambda>y\<^bsub>\<gamma>\<^esub>. B"
  define \<psi> where "\<psi> = \<phi>((x, \<alpha>) := \<V> \<phi> A)"
  from assms(1,2) and \<psi>_def have "\<psi> \<leadsto> \<D>"
    using \<V>_is_wff_denotation_function by simp
  {
    fix z
    assume "z \<in> elts (\<D> \<gamma>)"
    define \<phi>' where "\<phi>' = \<phi>((y, \<gamma>) := z)"
    from assms(1) and \<open>z \<in> elts (\<D> \<gamma>)\<close> and \<phi>'_def have "\<phi>' \<leadsto> \<D>"
      by simp
    moreover from \<phi>'_def and assms(4) have "\<forall>v \<in> free_vars A. \<phi> v = \<phi>' v"
      using free_vars_in_all_vars by auto
    ultimately have "\<V> \<phi> A = \<V> \<phi>' A"
      using assms(1,2) and prop_5400 by blast
    with \<psi>_def and \<phi>'_def and assms(4) have "\<phi>'((x, \<alpha>) := \<V> \<phi>' A) = \<psi>((y, \<gamma>) := z)"
      by auto
    with \<open>\<psi> \<leadsto> \<D>\<close> and \<open>z \<in> elts (\<D> \<gamma>)\<close> and assms(3) have "\<V> \<psi> ?D \<bullet> z = \<V> (\<psi>((y, \<gamma>) := z)) B"
      by (simp add: mixed_beta_conversion)
    also from \<open>\<phi>' \<leadsto> \<D>\<close> and assms(2,3) have "\<dots> = \<V> \<phi>' ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A)"
      using prop_5401_a and \<open>\<phi>'((x, \<alpha>) := \<V> \<phi>' A) = \<psi>((y, \<gamma>) := z)\<close> by simp
    also from \<phi>'_def and assms(1) and \<open>z \<in> elts (\<D> \<gamma>)\<close> and \<open>?A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> ?B \<in> wffs\<^bsub>o\<^esub>\<close>
    have "\<dots> = \<V> \<phi> ?B \<bullet> z"
      by (metis mixed_beta_conversion wffs_from_abs wffs_from_equality(2))
    finally have "\<V> \<psi> ?D \<bullet> z = \<V> \<phi> ?B \<bullet> z" .
  }
  note * = this
  then have "\<V> \<psi> ?D = \<V> \<phi> ?B"
  proof -
    from \<open>\<psi> \<leadsto> \<D>\<close> and assms(3) have "\<V> \<psi> ?D = (\<^bold>\<lambda>z \<^bold>: \<D> \<gamma>\<^bold>. \<V> (\<psi>((y, \<gamma>) := z)) B)"
      using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by simp
    moreover from assms(1) have "\<V> \<phi> ?B = (\<^bold>\<lambda>z \<^bold>: \<D> \<gamma>\<^bold>. \<V> (\<phi>((y, \<gamma>) := z)) ((\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A))"
      using wffs_from_abs[OF wffs_from_equality(2)[OF \<open>?A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> ?B \<in> wffs\<^bsub>o\<^esub>\<close>]]
      and wff_abs_denotation[OF \<V>_is_wff_denotation_function] by meson
    ultimately show ?thesis
      using vlambda_extensionality and * by fastforce
  qed
  with assms(1-3) and \<psi>_def have "\<V> \<phi> ?A = \<V> \<phi> ?B"
    using prop_5401_a and wffs_of_type_intros(4) by metis
  with assms(1) show ?thesis
    using prop_5401_b and wffs_from_equality[OF \<open>?A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> ?B \<in> wffs\<^bsub>o\<^esub>\<close>] by blast
qed

lemma axiom_4_4_validity:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<delta>\<^esub>"
  and "(y, \<gamma>) \<notin> {(x, \<alpha>)} \<union> vars A"
  shows "\<Turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>y\<^bsub>\<gamma>\<^esub>. B) \<sqdot> A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> (\<lambda>y\<^bsub>\<gamma>\<^esub>. (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A)" (is "\<Turnstile> ?A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> ?B")
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> ?A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> ?B"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover from assms and * and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> (?A =\<^bsub>\<gamma>\<rightarrow>\<delta>\<^esub> ?B) = \<^bold>T"
      using general_model.axiom_4_4_validity_aux by blast
    ultimately show ?thesis
      by simp
  qed
qed

lemma (in general_model) axiom_4_5_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<delta>\<^esub>"
  shows "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<alpha>\<rightarrow>\<delta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)) = \<^bold>T"
proof -
  define \<psi> where "\<psi> = \<phi>((x, \<alpha>) := \<V> \<phi> A)"
  from assms have wff: "(\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<alpha>\<rightarrow>\<delta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<in> wffs\<^bsub>o\<^esub>"
    using axioms.axiom_4_5 and axioms_are_wffs_of_type_o by blast
  with assms(1,2) and \<psi>_def have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) = \<V> \<psi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
    using prop_5401_a and wffs_from_equality(2) by blast
  also have "\<dots> = \<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
  proof -
    have "(x, \<alpha>) \<notin> free_vars (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
      by simp
    with \<psi>_def have "\<forall>v \<in> free_vars (\<lambda>x\<^bsub>\<alpha>\<^esub>. B). \<phi> v = \<psi> v"
      by simp
    moreover from \<psi>_def and assms(1,2) have "\<psi> \<leadsto> \<D>"
      using \<V>_is_wff_denotation_function by simp
    moreover from assms(2,3) have "(\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<in> wffs\<^bsub>\<alpha>\<rightarrow>\<delta>\<^esub>"
      by fastforce
    ultimately show ?thesis
      using assms(1) and prop_5400 by metis
  qed
  finally have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A) = \<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)" .
  with wff and assms(1) show ?thesis
    using prop_5401_b and wffs_from_equality by meson
qed

lemma axiom_4_5_validity:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<delta>\<^esub>"
  shows "\<Turnstile> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<alpha>\<rightarrow>\<delta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<alpha>\<rightarrow>\<delta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover
    from assms and * and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> ((\<lambda>x\<^bsub>\<alpha>\<^esub>. \<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<alpha>\<rightarrow>\<delta>\<^esub> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B)) = \<^bold>T"
      using general_model.axiom_4_5_validity_aux by blast
    ultimately show ?thesis
      by simp
  qed
qed

lemma (in general_model) axiom_5_validity_aux:
  assumes "\<phi> \<leadsto> \<D>"
  shows "\<V> \<phi> (\<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>) =\<^bsub>i\<^esub> \<yy>\<^bsub>i\<^esub>) = \<^bold>T"
proof -
  have "\<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>) =\<^bsub>i\<^esub> \<yy>\<^bsub>i\<^esub> \<in> wffs\<^bsub>o\<^esub>"
    using axioms.axiom_5 and axioms_are_wffs_of_type_o by blast
  have "Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub> \<in> wffs\<^bsub>i\<rightarrow>o\<^esub>"
    by blast
  with assms have "\<V> \<phi> (\<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>)) = \<V> \<phi> \<iota> \<bullet> \<V> \<phi> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>)"
    using \<V>_is_wff_denotation_function by blast
  also from assms have "\<dots> = \<V> \<phi> \<iota> \<bullet> (\<V> \<phi> (Q\<^bsub>i\<^esub>) \<bullet> \<V> \<phi> (\<yy>\<^bsub>i\<^esub>))"
    using wff_app_denotation[OF \<V>_is_wff_denotation_function] by (metis Q_wff wffs_of_type_intros(1))
  also from assms have "\<dots> = \<J> (\<cc>\<^sub>\<iota>, (i\<rightarrow>o)\<rightarrow>i) \<bullet> (\<J> (\<cc>\<^sub>Q, i\<rightarrow>i\<rightarrow>o) \<bullet> \<V> \<phi> (\<yy>\<^bsub>i\<^esub>))"
    using \<V>_is_wff_denotation_function by auto
  also from assms have "\<dots> = \<J> (\<cc>\<^sub>\<iota>, (i\<rightarrow>o)\<rightarrow>i) \<bullet> ((q\<^bsub>i\<^esub>\<^bsup>\<D>\<^esup>) \<bullet> \<V> \<phi> (\<yy>\<^bsub>i\<^esub>))"
    using Q_constant_of_type_def and Q_denotation by simp
  also from assms have "\<dots> = \<J> (\<cc>\<^sub>\<iota>, (i\<rightarrow>o)\<rightarrow>i) \<bullet> {\<V> \<phi> (\<yy>\<^bsub>i\<^esub>)}\<^bsub>i\<^esub>\<^bsup>\<D>\<^esup>"
    using \<V>_is_wff_denotation_function by auto
  finally have "\<V> \<phi> (\<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>)) = \<J> (\<cc>\<^sub>\<iota>, (i\<rightarrow>o)\<rightarrow>i) \<bullet> {\<V> \<phi> (\<yy>\<^bsub>i\<^esub>)}\<^bsub>i\<^esub>\<^bsup>\<D>\<^esup>" .
  moreover from assms have "\<J> (\<cc>\<^sub>\<iota>, (i\<rightarrow>o)\<rightarrow>i) \<bullet> {\<V> \<phi> (\<yy>\<^bsub>i\<^esub>)}\<^bsub>i\<^esub>\<^bsup>\<D>\<^esup> = \<V> \<phi> (\<yy>\<^bsub>i\<^esub>)"
    using \<V>_is_wff_denotation_function and \<iota>_denotation by force
  ultimately have "\<V> \<phi> (\<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>)) = \<V> \<phi> (\<yy>\<^bsub>i\<^esub>)"
    by (simp only:)
  with assms and \<open>Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub> \<in> wffs\<^bsub>i\<rightarrow>o\<^esub>\<close> show ?thesis
    using prop_5401_b by blast
qed

lemma axiom_5_validity:
  shows "\<Turnstile> \<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>) =\<^bsub>i\<^esub> \<yy>\<^bsub>i\<^esub>"
proof (intro allI impI)
  fix \<M> and \<phi>
  assume *: "is_general_model \<M>" "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> \<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>) =\<^bsub>i\<^esub> \<yy>\<^bsub>i\<^esub>"
  proof -
    obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
      using prod_cases3 by blast
    moreover from * and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> have "\<V> \<phi> (\<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> \<yy>\<^bsub>i\<^esub>) =\<^bsub>i\<^esub> \<yy>\<^bsub>i\<^esub>) = \<^bold>T"
      using general_model.axiom_5_validity_aux by simp
    ultimately show ?thesis
      by simp
  qed
qed

lemma axioms_validity:
  assumes "A \<in> axioms"
  shows "\<Turnstile> A"
  using assms
  and axiom_1_validity
  and axiom_2_validity
  and axiom_3_validity
  and axiom_4_1_con_validity
  and axiom_4_1_var_validity
  and axiom_4_2_validity
  and axiom_4_3_validity
  and axiom_4_4_validity
  and axiom_4_5_validity
  and axiom_5_validity
  by cases auto

lemma (in general_model) rule_R_validity_aux:
  assumes "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "\<forall>\<phi>. \<phi> \<leadsto> \<D> \<longrightarrow> \<V> \<phi> A = \<V> \<phi> B"
  and "C \<in> wffs\<^bsub>\<beta>\<^esub>" and "C' \<in> wffs\<^bsub>\<beta>\<^esub>"
  and "p \<in> positions C" and "A \<preceq>\<^bsub>p\<^esub> C" and "C\<lblot>p \<leftarrow> B\<rblot> \<rhd> C'"
  shows "\<forall>\<phi>. \<phi> \<leadsto> \<D> \<longrightarrow> \<V> \<phi> C = \<V> \<phi> C'"
proof -
  from assms(8,3-5,7) show ?thesis
  proof (induction arbitrary: \<beta>)
    case pos_found
    then show ?case
      by simp
  next
    case (replace_left_app p G B' G' H)
    show ?case
    proof (intro allI impI)
      fix \<phi>
      assume "\<phi> \<leadsto> \<D>"
      from \<open>G \<sqdot> H \<in> wffs\<^bsub>\<beta>\<^esub>\<close> obtain \<gamma> where "G \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>" and "H \<in> wffs\<^bsub>\<gamma>\<^esub>"
        by (rule wffs_from_app)
      with \<open>G' \<sqdot> H \<in> wffs\<^bsub>\<beta>\<^esub>\<close> have "G' \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>"
        by (metis wff_has_unique_type wffs_from_app)
      from assms(1) and \<open>\<phi> \<leadsto> \<D>\<close> and \<open>G \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>\<close> and \<open>H \<in> wffs\<^bsub>\<gamma>\<^esub>\<close>
      have "\<V> \<phi> (G \<sqdot> H) = \<V> \<phi> G \<bullet> \<V> \<phi> H"
        using \<V>_is_wff_denotation_function by blast
      also from \<open>\<phi> \<leadsto> \<D>\<close> and \<open>G \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>\<close> and \<open>G' \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>\<close> have "\<dots> = \<V> \<phi> G' \<bullet> \<V> \<phi> H"
        using replace_left_app.IH and replace_left_app.prems(1,4) by simp
      also from assms(1) and \<open>\<phi> \<leadsto> \<D>\<close> and \<open>G' \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>\<close> and \<open>H \<in> wffs\<^bsub>\<gamma>\<^esub>\<close>
      have "\<dots> = \<V> \<phi> (G' \<sqdot> H)"
        using \<V>_is_wff_denotation_function by fastforce
      finally show "\<V> \<phi> (G \<sqdot> H) = \<V> \<phi> (G' \<sqdot> H)" .
    qed
  next
    case (replace_right_app p H B' H' G)
    show ?case
    proof (intro allI impI)
      fix \<phi>
      assume "\<phi> \<leadsto> \<D>"
      from \<open>G \<sqdot> H \<in> wffs\<^bsub>\<beta>\<^esub>\<close> obtain \<gamma> where "G \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>" and "H \<in> wffs\<^bsub>\<gamma>\<^esub>"
        by (rule wffs_from_app)
      with \<open>G \<sqdot> H' \<in> wffs\<^bsub>\<beta>\<^esub>\<close> have "H' \<in> wffs\<^bsub>\<gamma>\<^esub>"
        using wff_has_unique_type and wffs_from_app by (metis type.inject)
      from assms(1) and \<open>\<phi> \<leadsto> \<D>\<close> and \<open>G \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>\<close> and \<open>H \<in> wffs\<^bsub>\<gamma>\<^esub>\<close>
      have "\<V> \<phi> (G \<sqdot> H) = \<V> \<phi> G \<bullet> \<V> \<phi> H"
        using \<V>_is_wff_denotation_function by blast
      also from \<open>\<phi> \<leadsto> \<D>\<close> and \<open>H \<in> wffs\<^bsub>\<gamma>\<^esub>\<close> and \<open>H' \<in> wffs\<^bsub>\<gamma>\<^esub>\<close> have "\<dots> = \<V> \<phi> G \<bullet> \<V> \<phi> H'"
        using replace_right_app.IH and replace_right_app.prems(1,4) by force
      also from assms(1) and \<open>\<phi> \<leadsto> \<D>\<close> and \<open>G \<in> wffs\<^bsub>\<gamma>\<rightarrow>\<beta>\<^esub>\<close> and \<open>H' \<in> wffs\<^bsub>\<gamma>\<^esub>\<close>
      have "\<dots> = \<V> \<phi> (G \<sqdot> H')"
        using \<V>_is_wff_denotation_function by fastforce
      finally show "\<V> \<phi> (G \<sqdot> H) = \<V> \<phi> (G \<sqdot> H')" .
    qed
  next
    case (replace_abs p E B' E' x \<gamma>)
    show ?case
    proof (intro allI impI)
      fix \<phi>
      assume "\<phi> \<leadsto> \<D>"
      define \<psi> where "\<psi> z = \<phi>((x, \<gamma>) := z)" for z
      with \<open>\<phi> \<leadsto> \<D>\<close> have \<psi>_assg: "\<psi> z \<leadsto> \<D>" if "z \<in> elts (\<D> \<gamma>)" for z
        by (simp add: that)
      from \<open>\<lambda>x\<^bsub>\<gamma>\<^esub>. E \<in> wffs\<^bsub>\<beta>\<^esub>\<close> obtain \<delta> where "\<beta> = \<gamma>\<rightarrow>\<delta>" and "E \<in> wffs\<^bsub>\<delta>\<^esub>"
        by (rule wffs_from_abs)
      with \<open>\<lambda>x\<^bsub>\<gamma>\<^esub>. E' \<in> wffs\<^bsub>\<beta>\<^esub>\<close> have "E' \<in> wffs\<^bsub>\<delta>\<^esub>"
        using wffs_from_abs by blast
      from assms(1) and \<open>\<phi> \<leadsto> \<D>\<close> and \<open>E \<in> wffs\<^bsub>\<delta>\<^esub>\<close> and \<psi>_def
      have "\<V> \<phi> (\<lambda>x\<^bsub>\<gamma>\<^esub>. E) = (\<^bold>\<lambda>z \<^bold>: \<D> \<gamma>\<^bold>. \<V> (\<psi> z) E)"
        using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by simp
      also have "\<dots> = (\<^bold>\<lambda>z \<^bold>: \<D> \<gamma>\<^bold>. \<V> (\<psi> z) E')"
      proof (intro vlambda_extensionality)
        fix z
        assume "z \<in> elts (\<D> \<gamma>)"
        from \<open>E \<in> wffs\<^bsub>\<delta>\<^esub>\<close> and \<open>E' \<in> wffs\<^bsub>\<delta>\<^esub>\<close> have "\<forall>\<phi>. \<phi> \<leadsto> \<D> \<longrightarrow> \<V> \<phi> E = \<V> \<phi> E'"
          using replace_abs.prems(1,4) and replace_abs.IH by simp
        with \<psi>_assg and \<open>z \<in> elts (\<D> \<gamma>)\<close> show "\<V> (\<psi> z) E = \<V> (\<psi> z) E'"
          by simp
      qed
      also from assms(1) and \<open>\<phi> \<leadsto> \<D>\<close> and \<open>E' \<in> wffs\<^bsub>\<delta>\<^esub>\<close> and \<psi>_def
      have "\<dots> = \<V> \<phi> (\<lambda>x\<^bsub>\<gamma>\<^esub>. E')"
        using wff_abs_denotation[OF \<V>_is_wff_denotation_function] by simp
      finally show "\<V> \<phi> (\<lambda>x\<^bsub>\<gamma>\<^esub>. E) = \<V> \<phi> (\<lambda>x\<^bsub>\<gamma>\<^esub>. E')" .
    qed
  qed
qed

lemma rule_R_validity:
  assumes "C \<in> wffs\<^bsub>o\<^esub>" and "C' \<in> wffs\<^bsub>o\<^esub>" and "E \<in> wffs\<^bsub>o\<^esub>"
  and "\<Turnstile> C" and "\<Turnstile> E"
  and "is_rule_R_app p C' C E"
  shows "\<Turnstile> C'"
proof (intro allI impI)
  fix \<M> and \<phi>
  assume "is_general_model \<M>" and "\<phi> \<leadsto>\<^sub>M \<M>"
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> C'"
  proof -
    have "\<M> \<Turnstile> C'"
    proof -
      obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
        using prod_cases3 by blast
      from assms(6) obtain A and B and \<alpha> where "A \<in> wffs\<^bsub>\<alpha>\<^esub>" and "B \<in> wffs\<^bsub>\<alpha>\<^esub>" and "E = A =\<^bsub>\<alpha>\<^esub> B"
        using wffs_from_equality by (meson is_rule_R_app_def)
      note * = \<open>is_general_model \<M>\<close> \<open>\<M> = (\<D>, \<J>, \<V>)\<close> \<open>\<phi> \<leadsto>\<^sub>M \<M>\<close>
      have "\<V> \<phi>' C = \<V> \<phi>' C'" if "\<phi>' \<leadsto> \<D>" for \<phi>'
      proof -
        from assms(5) and *(1,2) and \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>E = A =\<^bsub>\<alpha>\<^esub> B\<close> and that
        have "\<forall>\<phi>'. \<phi>' \<leadsto> \<D> \<longrightarrow>\<V> \<phi>' A = \<V> \<phi>' B"
          using general_model.prop_5401_b by blast
        moreover
        from \<open>E = A =\<^bsub>\<alpha>\<^esub> B\<close> and assms(6) have "p \<in> positions C" and "A \<preceq>\<^bsub>p\<^esub> C" and "C\<lblot>p \<leftarrow> B\<rblot> \<rhd> C'"
          using is_subform_implies_in_positions by auto
        ultimately show ?thesis
          using \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>C \<in> wffs\<^bsub>o\<^esub>\<close> and assms(2) and that and *(1,2)
          and general_model.rule_R_validity_aux by blast
      qed
      with assms(4) and *(1,2) show ?thesis
        by simp
    qed
    with \<open>\<phi> \<leadsto>\<^sub>M \<M>\<close> show ?thesis
      by blast
  qed
qed

lemma individual_proof_step_validity:
  assumes "is_proof \<S>" and "A \<in> lset \<S>"
  shows "\<Turnstile> A"
using assms proof (induction "length \<S>" arbitrary: \<S> A rule: less_induct)
  case less
  from \<open>A \<in> lset \<S>\<close> obtain i' where "\<S> ! i' = A" and "\<S> \<noteq> []" and "i' < length \<S>"
    by (metis empty_iff empty_set in_set_conv_nth)
  with \<open>is_proof \<S>\<close> have "is_proof (take (Suc i') \<S>)" and "take (Suc i') \<S> \<noteq> []"
    using proof_prefix_is_proof[where \<S>\<^sub>1 = "take (Suc i') \<S>" and \<S>\<^sub>2 = "drop (Suc i') \<S>"]
    and append_take_drop_id by simp_all
  from \<open>i' < length \<S>\<close> consider (a) "i' < length \<S> - 1" | (b) "i' = length \<S> - 1"
    by fastforce
  then show ?case
  proof cases
    case a
    then have "length (take (Suc i') \<S>) < length \<S>"
      by simp
    with \<open>\<S> ! i' = A\<close> and \<open>take (Suc i') \<S> \<noteq> []\<close> have "A \<in> lset (take (Suc i') \<S>)"
      by (simp add: take_Suc_conv_app_nth)
    with \<open>length (take (Suc i') \<S>) < length \<S>\<close> and \<open>is_proof (take (Suc i') \<S>)\<close> show ?thesis
      using less(1) by blast
  next
    case b
    with \<open>\<S> ! i' = A\<close> and \<open>\<S> \<noteq> []\<close> have "last \<S> = A"
      using last_conv_nth by blast
    with \<open>is_proof \<S>\<close> and \<open>\<S> \<noteq> []\<close> and b have "is_proof_step \<S> i'"
      using added_suffix_proof_preservation[where \<S>' = "[]"] by simp
    then consider
      (axiom) "\<S> ! i' \<in> axioms"
    | (rule_R) "\<exists>p j k. {j, k} \<subseteq> {0..<i'} \<and> is_rule_R_app p (\<S> ! i') (\<S> ! j) (\<S> ! k)"
      by fastforce
    then show ?thesis
    proof cases
      case axiom
      with \<open>\<S> ! i' = A\<close> show ?thesis
        by (blast dest: axioms_validity)
    next
      case rule_R
      then obtain p and j and k
        where "{j, k} \<subseteq> {0..<i'}" and "is_rule_R_app p (\<S> ! i') (\<S> ! j) (\<S> ! k)"
        by blast
      let ?\<S>\<^sub>j = "take (Suc j) \<S>" and ?\<S>\<^sub>k = "take (Suc k) \<S>"
      obtain \<S>\<^sub>j' and \<S>\<^sub>k' where "\<S> = ?\<S>\<^sub>j @ \<S>\<^sub>j'" and "\<S> = ?\<S>\<^sub>k @ \<S>\<^sub>k'"
        by (metis append_take_drop_id)
      with \<open>is_proof \<S>\<close> have "is_proof (?\<S>\<^sub>j @ \<S>\<^sub>j')" and "is_proof (?\<S>\<^sub>k @ \<S>\<^sub>k')"
        by (simp_all only:)
      moreover from \<open>\<S> \<noteq> []\<close> have "?\<S>\<^sub>j \<noteq> []" and "?\<S>\<^sub>k \<noteq> []"
        by simp_all
      ultimately have "is_proof_of ?\<S>\<^sub>j (last ?\<S>\<^sub>j)" and "is_proof_of ?\<S>\<^sub>k (last ?\<S>\<^sub>k)"
        using proof_prefix_is_proof_of_last[where \<S> = ?\<S>\<^sub>j and \<S>' = \<S>\<^sub>j']
        and proof_prefix_is_proof_of_last[where \<S> = ?\<S>\<^sub>k and \<S>' = \<S>\<^sub>k']
        by fastforce+
      moreover
      from \<open>{j, k} \<subseteq> {0..<i'}\<close> and b have "length ?\<S>\<^sub>j < length \<S>" and "length ?\<S>\<^sub>k < length \<S>"
        by force+
      moreover from calculation(3,4) have "\<S> ! j \<in> lset ?\<S>\<^sub>j" and "\<S> ! k \<in> lset ?\<S>\<^sub>k"
        by (simp_all add: take_Suc_conv_app_nth)
      ultimately have "\<Turnstile> \<S> ! j" and "\<Turnstile> \<S> ! k"
        using \<open>?\<S>\<^sub>j \<noteq> []\<close> and \<open>?\<S>\<^sub>k \<noteq> []\<close> and less(1) unfolding is_proof_of_def by presburger+
      moreover have "\<S> ! i' \<in> wffs\<^bsub>o\<^esub>" and "\<S> ! j \<in> wffs\<^bsub>o\<^esub>" and "\<S> ! k \<in> wffs\<^bsub>o\<^esub>"
        using \<open>is_rule_R_app p (\<S> ! i') (\<S> ! j) (\<S> ! k)\<close> and replacement_preserves_typing
        by force+
      ultimately show ?thesis
        using \<open>is_rule_R_app p (\<S> ! i') (\<S> ! j) (\<S> ! k)\<close> and \<open>\<S> ! i' = A\<close>
        and rule_R_validity[where C' = A] by blast
    qed
  qed
qed

lemma semantic_modus_ponens:
  assumes "is_general_model \<M>"
  and "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  and "\<M> \<Turnstile> A \<supset>\<^sup>\<Q> B"
  and "\<M> \<Turnstile> A"
  shows "\<M> \<Turnstile> B"
proof (intro allI impI)
  fix \<phi>
  assume "\<phi> \<leadsto>\<^sub>M \<M>"
  moreover obtain \<D> and \<J> and \<V> where "\<M> = (\<D>, \<J>, \<V>)"
    using prod_cases3 by blast
  ultimately have "\<phi> \<leadsto> \<D>"
    by simp
  show "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> B"
  proof -
    from assms(4) have "\<V> \<phi> (A \<supset>\<^sup>\<Q> B) = \<^bold>T"
      using \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and \<open>\<phi> \<leadsto>\<^sub>M \<M>\<close> by auto
    with assms(1-3) have "\<V> \<phi> A \<^bold>\<supset> \<V> \<phi> B = \<^bold>T"
      using \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and \<open>\<phi> \<leadsto>\<^sub>M \<M>\<close> and general_model.prop_5401_f' by simp
    moreover from assms(5) have "\<V> \<phi> A = \<^bold>T"
      using \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and \<open>\<phi> \<leadsto> \<D>\<close> by auto
    moreover from \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and assms(1) have "elts (\<D> o) = elts \<bool>"
      using frame.truth_values_domain_def and general_model_def and premodel_def by fastforce
    with assms and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and \<open>\<phi> \<leadsto> \<D>\<close> and \<open>\<V> \<phi> A = \<^bold>T\<close> have "{\<V> \<phi> A, \<V> \<phi> B} \<subseteq> elts \<bool>"
      using general_model.\<V>_is_wff_denotation_function
      and premodel.wff_denotation_function_is_domain_respecting and general_model.axioms(1) by blast
    ultimately have "\<V> \<phi> B = \<^bold>T"
      by fastforce
    with \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and assms(1) and \<open>\<phi> \<leadsto> \<D>\<close> show ?thesis
      by simp
  qed
qed

lemma generalized_semantic_modus_ponens:
  assumes "is_general_model \<M>"
  and "lset hs \<subseteq> wffs\<^bsub>o\<^esub>"
  and "\<forall>H \<in> lset hs. \<M> \<Turnstile> H"
  and "P \<in> wffs\<^bsub>o\<^esub>"
  and "\<M> \<Turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> P"
  shows "\<M> \<Turnstile> P"
using assms(2-5) proof (induction hs arbitrary: P rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc H' hs)
  from \<open>\<M> \<Turnstile> (hs @ [H']) \<supset>\<^sup>\<Q>\<^sub>\<star> P\<close> have "\<M> \<Turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> (H' \<supset>\<^sup>\<Q> P)"
    by simp
  moreover from \<open>\<forall>H \<in> lset (hs @ [H']). \<M> \<Turnstile> H\<close> and \<open>lset (hs @ [H']) \<subseteq> wffs\<^bsub>o\<^esub>\<close>
  have "\<forall>H \<in> lset hs. \<M> \<Turnstile> H" and "lset hs \<subseteq> wffs\<^bsub>o\<^esub>"
    by simp_all
  moreover from \<open>lset (hs @ [H']) \<subseteq> wffs\<^bsub>o\<^esub>\<close> and \<open>P \<in> wffs\<^bsub>o\<^esub>\<close> have "H' \<supset>\<^sup>\<Q> P \<in> wffs\<^bsub>o\<^esub>"
    by auto
  ultimately have "\<M> \<Turnstile> H' \<supset>\<^sup>\<Q> P"
    by (elim snoc.IH)
  moreover from \<open>\<forall>H \<in> lset (hs @ [H']). \<M> \<Turnstile> H\<close> have "\<M> \<Turnstile> H'"
    by simp
  moreover from \<open>H' \<supset>\<^sup>\<Q> P \<in> wffs\<^bsub>o\<^esub>\<close> have "H' \<in> wffs\<^bsub>o\<^esub>"
    using wffs_from_imp_op(1) by blast
  ultimately show ?case
    using assms(1) and \<open>P \<in> wffs\<^bsub>o\<^esub>\<close> and semantic_modus_ponens by simp
qed

subsection \<open>Proposition 5402(a)\<close>

proposition theoremhood_implies_validity:
  assumes "is_theorem A"
  shows "\<Turnstile> A"
  using assms and individual_proof_step_validity by force

subsection \<open>Proposition 5402(b)\<close>

proposition hyp_derivability_implies_validity:
  assumes "is_hyps \<G>"
  and "is_model_for \<M> \<G>"
  and "\<G> \<turnstile> A"
  and "is_general_model \<M>"
  shows "\<M> \<Turnstile> A"
proof -
  from assms(3) have "A \<in> wffs\<^bsub>o\<^esub>"
    by (fact hyp_derivable_form_is_wffso)
  from \<open>\<G> \<turnstile> A\<close> and \<open>is_hyps \<G>\<close> obtain \<H> where "finite \<H>" and "\<H> \<subseteq> \<G>" and "\<H> \<turnstile> A"
    by blast
  moreover from \<open>finite \<H>\<close> obtain hs where "lset hs = \<H>"
    using finite_list by blast
  ultimately have "\<turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> A"
    using generalized_deduction_theorem by simp
  with assms(4) have "\<M> \<Turnstile> hs \<supset>\<^sup>\<Q>\<^sub>\<star> A"
    using derivability_from_no_hyps_theoremhood_equivalence and theoremhood_implies_validity
    by blast
  moreover from \<open>\<H> \<subseteq> \<G>\<close> and assms(2) have "\<M> \<Turnstile> H" if "H \<in> \<H>" for H
    using that by blast
  moreover from \<open>\<H> \<subseteq> \<G>\<close> and \<open>lset hs = \<H>\<close> and assms(1) have "lset hs \<subseteq> wffs\<^bsub>o\<^esub>"
    by blast
  ultimately show ?thesis
    using assms(1,4) and \<open>A \<in> wffs\<^bsub>o\<^esub>\<close> and \<open>lset hs = \<H>\<close> and generalized_semantic_modus_ponens
    by auto
qed

subsection \<open>Theorem 5402 (Soundness Theorem)\<close>

lemmas thm_5402 = theoremhood_implies_validity hyp_derivability_implies_validity

end
