(*  Title:      Stateful_Protocol_Verification.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section\<open>Stateful Protocol Verification\<close>
theory Stateful_Protocol_Verification
imports Stateful_Protocol_Model Term_Implication
begin

subsection \<open>Fixed-Point Intruder Deduction Lemma\<close>
context stateful_protocol_model
begin

abbreviation pubval_terms::"('fun,'atom,'sets,'lbl) prot_terms" where
  "pubval_terms \<equiv> {t. \<exists>f \<in> funs_term t. is_PubConstValue f}"

abbreviation abs_terms::"('fun,'atom,'sets,'lbl) prot_terms" where
  "abs_terms \<equiv> {t. \<exists>f \<in> funs_term t. is_Abs f}"

definition intruder_deduct_GSMP::
  "[('fun,'atom,'sets,'lbl) prot_terms,
    ('fun,'atom,'sets,'lbl) prot_terms,
    ('fun,'atom,'sets,'lbl) prot_term]
    \<Rightarrow> bool" ("\<langle>_;_\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P _" 50)
where
  "\<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t \<equiv> intruder_deduct_restricted M (\<lambda>t. t \<in> GSMP T - (pubval_terms \<union> abs_terms)) t"

lemma intruder_deduct_GSMP_induct[consumes 1, case_names AxiomH ComposeH DecomposeH]:
  assumes "\<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t" "\<And>t. t \<in> M \<Longrightarrow> P M t"
          "\<And>S f. \<lbrakk>length S = arity f; public f;
                  \<And>s. s \<in> set S \<Longrightarrow> \<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P s;
                  \<And>s. s \<in> set S \<Longrightarrow> P M s;
                  Fun f S \<in> GSMP T - (pubval_terms \<union> abs_terms)
                  \<rbrakk> \<Longrightarrow> P M (Fun f S)"
          "\<And>t K T' t\<^sub>i. \<lbrakk>\<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t; P M t; Ana t = (K, T'); \<And>k. k \<in> set K \<Longrightarrow> \<langle>M; T\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P k;
                        \<And>k. k \<in> set K \<Longrightarrow> P M k; t\<^sub>i \<in> set T'\<rbrakk> \<Longrightarrow> P M t\<^sub>i"
  shows "P M t"
proof -
  let ?Q = "\<lambda>t. t \<in> GSMP T - (pubval_terms \<union> abs_terms)"
  show ?thesis
    using intruder_deduct_restricted_induct[of M ?Q t "\<lambda>M Q t. P M t"] assms
    unfolding intruder_deduct_GSMP_def
    by blast
qed

lemma pubval_terms_subst:
  assumes "t \<cdot> \<theta> \<in> pubval_terms" "\<theta> ` fv t \<inter> pubval_terms = {}"
  shows "t \<in> pubval_terms"
using assms(1,2)
proof (induction t)
  case (Fun f T)
  let ?P = "\<lambda>f. is_PubConstValue f"
  from Fun show ?case
  proof (cases "?P f")
    case False
    then obtain t where t: "t \<in> set T" "t \<cdot> \<theta> \<in> pubval_terms"
      using Fun.prems by auto
    hence "\<theta> ` fv t \<inter> pubval_terms = {}" using Fun.prems(2) by auto
    thus ?thesis using Fun.IH[OF t] t(1) by auto
  qed force
qed simp

lemma abs_terms_subst:
  assumes "t \<cdot> \<theta> \<in> abs_terms" "\<theta> ` fv t \<inter> abs_terms = {}"
  shows "t \<in> abs_terms"
using assms(1,2)
proof (induction t)
  case (Fun f T)
  let ?P = "\<lambda>f. is_Abs f"
  from Fun show ?case
  proof (cases "?P f")
    case False
    then obtain t where t: "t \<in> set T" "t \<cdot> \<theta> \<in> abs_terms"
      using Fun.prems by auto
    hence "\<theta> ` fv t \<inter> abs_terms = {}" using Fun.prems(2) by auto
    thus ?thesis using Fun.IH[OF t] t(1) by auto
  qed force
qed simp

lemma pubval_terms_subst':
  assumes "t \<cdot> \<theta> \<in> pubval_terms" "\<forall>n. PubConst Value n \<notin> \<Union>(funs_term ` (\<theta> ` fv t))"
  shows "t \<in> pubval_terms"
proof -
  have False
    when fs: "f \<in> funs_term s" "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv t)" "is_PubConstValue f"
    for f s
  proof -
    obtain T where T: "Fun f T \<in> subterms s" using funs_term_Fun_subterm[OF fs(1)] by moura
    hence "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv t)" using fs(2) in_subterms_subset_Union by blast
    thus ?thesis
      using assms(2) funs_term_Fun_subterm'[of f T] fs(3)
      unfolding is_PubConstValue_def
      by (cases f) force+
  qed
  thus ?thesis using pubval_terms_subst[OF assms(1)] by auto
qed

lemma abs_terms_subst':
  assumes "t \<cdot> \<theta> \<in> abs_terms" "\<forall>n. Abs n \<notin> \<Union>(funs_term ` (\<theta> ` fv t))"
  shows "t \<in> abs_terms"
proof -
  have "\<not>is_Abs f" when fs: "f \<in> funs_term s" "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv t)" for f s
  proof -
    obtain T where T: "Fun f T \<in> subterms s" using funs_term_Fun_subterm[OF fs(1)] by moura  
    hence "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (\<theta> ` fv t)" using fs(2) in_subterms_subset_Union by blast
    thus ?thesis using assms(2) funs_term_Fun_subterm'[of f T] by (cases f) auto
  qed
  thus ?thesis using abs_terms_subst[OF assms(1)] by force
qed

lemma pubval_terms_subst_range_disj:
  "subst_range \<theta> \<inter> pubval_terms = {} \<Longrightarrow> \<theta> ` fv t \<inter> pubval_terms = {}"
proof (induction t)
  case (Var x) thus ?case by (cases "x \<in> subst_domain \<theta>") auto
qed auto

lemma abs_terms_subst_range_disj:
  "subst_range \<theta> \<inter> abs_terms = {} \<Longrightarrow> \<theta> ` fv t \<inter> abs_terms = {}"
proof (induction t)
  case (Var x) thus ?case by (cases "x \<in> subst_domain \<theta>") auto
qed auto

lemma pubval_terms_subst_range_comp:
  assumes "subst_range \<theta> \<inter> pubval_terms = {}" "subst_range \<delta> \<inter> pubval_terms = {}"
  shows "subst_range (\<theta> \<circ>\<^sub>s \<delta>) \<inter> pubval_terms = {}"
proof -
  { fix t f assume t:
      "t \<in> subst_range (\<theta> \<circ>\<^sub>s \<delta>)" "f \<in> funs_term t" "is_PubConstValue f"
    then obtain x where x: "(\<theta> \<circ>\<^sub>s \<delta>) x = t" by auto
    have "\<theta> x \<notin> pubval_terms" using assms(1) by (cases "\<theta> x \<in> subst_range \<theta>") force+
    hence "(\<theta> \<circ>\<^sub>s \<delta>) x \<notin> pubval_terms"
      using assms(2) pubval_terms_subst[of "\<theta> x" \<delta>] pubval_terms_subst_range_disj
      by (metis (mono_tags, lifting) subst_compose_def)
    hence False using t(2,3) x by blast
  } thus ?thesis by fast
qed

lemma pubval_terms_subst_range_comp':
  assumes "(\<theta> ` X) \<inter> pubval_terms = {}" "(\<delta> ` fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` X)) \<inter> pubval_terms = {}"
  shows "((\<theta> \<circ>\<^sub>s \<delta>) ` X) \<inter> pubval_terms = {}"
proof -
  { fix t f assume t:
      "t \<in> (\<theta> \<circ>\<^sub>s \<delta>) ` X" "f \<in> funs_term t" "is_PubConstValue f"
    then obtain x where x: "(\<theta> \<circ>\<^sub>s \<delta>) x = t" "x \<in> X" by auto
    have "\<theta> x \<notin> pubval_terms" using assms(1) x(2) by force
    moreover have "fv (\<theta> x) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` X)" using x(2) by (auto simp add: fv_subset)
    hence "\<delta> ` fv (\<theta> x) \<inter> pubval_terms = {}" using assms(2) by auto
    ultimately have "(\<theta> \<circ>\<^sub>s \<delta>) x \<notin> pubval_terms"
      using pubval_terms_subst[of "\<theta> x" \<delta>]
      by (metis (mono_tags, lifting) subst_compose_def)
    hence False using t(2,3) x by blast
  } thus ?thesis by fast
qed

lemma abs_terms_subst_range_comp:
  assumes "subst_range \<theta> \<inter> abs_terms = {}" "subst_range \<delta> \<inter> abs_terms = {}"
  shows "subst_range (\<theta> \<circ>\<^sub>s \<delta>) \<inter> abs_terms = {}"
proof -
  { fix t f assume t: "t \<in> subst_range (\<theta> \<circ>\<^sub>s \<delta>)" "f \<in> funs_term t" "is_Abs f"
    then obtain x where x: "(\<theta> \<circ>\<^sub>s \<delta>) x = t" by auto
    have "\<theta> x \<notin> abs_terms" using assms(1) by (cases "\<theta> x \<in> subst_range \<theta>") force+
    hence "(\<theta> \<circ>\<^sub>s \<delta>) x \<notin> abs_terms"
      using assms(2) abs_terms_subst[of "\<theta> x" \<delta>] abs_terms_subst_range_disj
      by (metis (mono_tags, lifting) subst_compose_def)
    hence False using t(2,3) x by blast
  } thus ?thesis by fast
qed

lemma abs_terms_subst_range_comp':
  assumes "(\<theta> ` X) \<inter> abs_terms = {}" "(\<delta> ` fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` X)) \<inter> abs_terms = {}"
  shows "((\<theta> \<circ>\<^sub>s \<delta>) ` X) \<inter> abs_terms = {}"
proof -
  { fix t f assume t:
      "t \<in> (\<theta> \<circ>\<^sub>s \<delta>) ` X" "f \<in> funs_term t" "is_Abs f"
    then obtain x where x: "(\<theta> \<circ>\<^sub>s \<delta>) x = t" "x \<in> X" by auto
    have "\<theta> x \<notin> abs_terms" using assms(1) x(2) by force
    moreover have "fv (\<theta> x) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` X)" using x(2) by (auto simp add: fv_subset)
    hence "\<delta> ` fv (\<theta> x) \<inter> abs_terms = {}" using assms(2) by auto
    ultimately have "(\<theta> \<circ>\<^sub>s \<delta>) x \<notin> abs_terms"
      using abs_terms_subst[of "\<theta> x" \<delta>]
      by (metis (mono_tags, lifting) subst_compose_def)
    hence False using t(2,3) x by blast
  } thus ?thesis by fast
qed

context
begin
private lemma Ana_abs_aux1:
  fixes \<delta>::"(('fun,'atom,'sets,'lbl) prot_fun, nat, ('fun,'atom,'sets,'lbl) prot_var) gsubst"
    and \<alpha>::"nat \<Rightarrow> 'sets set"
  assumes "Ana\<^sub>f f = (K,T)"
  shows "(K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>) \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
proof -
  { fix k assume "k \<in> set K"
    hence "k \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K)" by force
    hence "k \<cdot> \<delta> \<cdot>\<^sub>\<alpha> \<alpha> = k \<cdot> (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
    proof (induction k)
      case (Fun g S)
      have "\<And>s. s \<in> set S \<Longrightarrow> s \<cdot> \<delta> \<cdot>\<^sub>\<alpha> \<alpha> = s \<cdot> (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
        using Fun.IH in_subterms_subset_Union[OF Fun.prems] Fun_param_in_subterms[of _ S g]
        by (meson contra_subsetD)
      thus ?case using Ana\<^sub>f_assm1_alt[OF assms Fun.prems] by (cases g) auto
    qed simp
  } thus ?thesis unfolding abs_apply_list_def by force
qed

private lemma Ana_abs_aux2:
  fixes \<alpha>::"nat \<Rightarrow> 'sets set"
    and K::"(('fun,'atom,'sets,'lbl) prot_fun, nat) term list"
    and M::"nat list"
    and T::"('fun,'atom,'sets,'lbl) prot_term list"
  assumes "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K) \<union> set M. i < length T"
    and "(K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T) \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>n. T ! n \<cdot>\<^sub>\<alpha> \<alpha>)"
  shows "(K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T) \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T)" (is "?A1 = ?A2")
    and "(map ((!) T) M) \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = map ((!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T)) M" (is "?B1 = ?B2")
proof -
  have "T ! i \<cdot>\<^sub>\<alpha> \<alpha> = (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i" when "i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K)" for i
    using that assms(1) by auto
  hence "k \<cdot> (\<lambda>i. T ! i \<cdot>\<^sub>\<alpha> \<alpha>) = k \<cdot> (\<lambda>i. (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i)" when "k \<in> set K" for k
    using that term_subst_eq_conv[of k "\<lambda>i. T ! i \<cdot>\<^sub>\<alpha> \<alpha>" "\<lambda>i. (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i"]
    by auto
  thus "?A1 = ?A2" using assms(2) by (force simp add: abs_apply_terms_def)

  have "T ! i \<cdot>\<^sub>\<alpha> \<alpha> = map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T ! i" when "i \<in> set M" for i
    using that assms(1) by auto
  thus "?B1 = ?B2" by (force simp add: abs_apply_list_def)
qed

private lemma Ana_abs_aux1_set:
  fixes \<delta>::"(('fun,'atom,'sets,'lbl) prot_fun, nat, ('fun,'atom,'sets,'lbl) prot_var) gsubst"
    and \<alpha>::"nat \<Rightarrow> 'sets set"
  assumes "Ana\<^sub>f f = (K,T)"
  shows "(set K \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> = set K \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
proof -
  { fix k assume "k \<in> set K"
    hence "k \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set K)" by force
    hence "k \<cdot> \<delta> \<cdot>\<^sub>\<alpha> \<alpha> = k \<cdot> (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
    proof (induction k)
      case (Fun g S)
      have "\<And>s. s \<in> set S \<Longrightarrow> s \<cdot> \<delta> \<cdot>\<^sub>\<alpha> \<alpha> = s \<cdot> (\<lambda>n. \<delta> n \<cdot>\<^sub>\<alpha> \<alpha>)"
        using Fun.IH in_subterms_subset_Union[OF Fun.prems] Fun_param_in_subterms[of _ S g]
        by (meson contra_subsetD)
      thus ?case using Ana\<^sub>f_assm1_alt[OF assms Fun.prems] by (cases g) auto
    qed simp
  } thus ?thesis unfolding abs_apply_terms_def by force
qed

private lemma Ana_abs_aux2_set:
  fixes \<alpha>::"nat \<Rightarrow> 'sets set"
    and K::"(('fun,'atom,'sets,'lbl) prot_fun, nat) terms"
    and M::"nat set"
    and T::"('fun,'atom,'sets,'lbl) prot_term list"
  assumes "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t K \<union> M. i < length T"
    and "(K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) T) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> = K \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<lambda>n. T ! n \<cdot>\<^sub>\<alpha> \<alpha>)"
  shows "(K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) T) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> = K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T)" (is "?A1 = ?A2")
    and "((!) T ` M) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> = (!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ` M" (is "?B1 = ?B2")
proof -
  have "T ! i \<cdot>\<^sub>\<alpha> \<alpha> = (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i" when "i \<in> fv\<^sub>s\<^sub>e\<^sub>t K" for i
    using that assms(1) by auto
  hence "k \<cdot> (\<lambda>i. T ! i \<cdot>\<^sub>\<alpha> \<alpha>) = k \<cdot> (\<lambda>i. (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i)" when "k \<in> K" for k
    using that term_subst_eq_conv[of k "\<lambda>i. T ! i \<cdot>\<^sub>\<alpha> \<alpha>" "\<lambda>i. (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T) ! i"]
    by auto
  thus "?A1 = ?A2" using assms(2) by (force simp add: abs_apply_terms_def)

  have "T ! i \<cdot>\<^sub>\<alpha> \<alpha> = map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) T ! i" when "i \<in> M" for i
    using that assms(1) by auto
  thus "?B1 = ?B2" by (force simp add: abs_apply_terms_def)
qed

lemma Ana_abs:
  fixes t::"('fun,'atom,'sets,'lbl) prot_term"
  assumes "Ana t = (K, T)"
  shows "Ana (t \<cdot>\<^sub>\<alpha> \<alpha>) = (K \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>, T \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>)"
  using assms
proof (induction t rule: Ana.induct)
  case (1 f S)
  obtain K' T' where *: "Ana\<^sub>f f = (K',T')" by moura
  show ?case using 1
  proof (cases "arity\<^sub>f f = length S \<and> arity\<^sub>f f > 0")
    case True
    hence "K = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) S" "T = map ((!) S) T'"
        and **: "arity\<^sub>f f = length (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) S)" "arity\<^sub>f f > 0"
      using 1 * by auto
    hence "K \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = K' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) S)"
          "T \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> = map ((!) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) S)) T'"
      using Ana\<^sub>f_assm2_alt[OF *] Ana_abs_aux2[OF _ Ana_abs_aux1[OF *], of T' S \<alpha>]
      unfolding abs_apply_list_def
      by auto
    moreover have "Fun (Fu f) S \<cdot>\<^sub>\<alpha> \<alpha> = Fun (Fu f) (map (\<lambda>s. s \<cdot>\<^sub>\<alpha> \<alpha>) S)" by simp
    ultimately show ?thesis using Ana_Fu_intro[OF ** *] by metis
  qed (auto simp add: abs_apply_list_def)
qed (simp_all add: abs_apply_list_def)
end

lemma deduct_FP_if_deduct:
  fixes M IK FP::"('fun,'atom,'sets,'lbl) prot_terms"
  assumes IK: "IK \<subseteq> GSMP M - (pubval_terms \<union> abs_terms)" "\<forall>t \<in> IK \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>. FP \<turnstile>\<^sub>c t"
    and t: "IK \<turnstile> t" "t \<in> GSMP M - (pubval_terms \<union> abs_terms)"
  shows "FP \<turnstile> t \<cdot>\<^sub>\<alpha> \<alpha>"
proof -
  let ?P = "\<lambda>f. \<not>is_PubConstValue f"
  let ?GSMP = "GSMP M - (pubval_terms \<union> abs_terms)"

  have 1: "\<forall>m \<in> IK. m \<in> ?GSMP"
    using IK(1) by blast

  have 2: "\<forall>t t'. t \<in> ?GSMP \<longrightarrow> t' \<sqsubseteq> t \<longrightarrow> t' \<in> ?GSMP"
  proof (intro allI impI)
    fix t t' assume t: "t \<in> ?GSMP" "t' \<sqsubseteq> t"
    hence "t' \<in> GSMP M" using ground_subterm unfolding GSMP_def by auto
    moreover have "\<not>is_PubConstValue f"
      when "f \<in> funs_term t" for f
      using t(1) that by auto
    hence "\<not>is_PubConstValue f"
      when "f \<in> funs_term t'" for f
      using that subtermeq_imp_funs_term_subset[OF t(2)] by auto
    moreover have "\<not>is_Abs f" when "f \<in> funs_term t" for f using t(1) that by auto
    hence "\<not>is_Abs f" when "f \<in> funs_term t'" for f
      using that subtermeq_imp_funs_term_subset[OF t(2)] by auto
    ultimately show "t' \<in> ?GSMP" by simp
  qed

  have 3: "\<forall>t K T k. t \<in> ?GSMP \<longrightarrow> Ana t = (K, T) \<longrightarrow> k \<in> set K \<longrightarrow> k \<in> ?GSMP"
  proof (intro allI impI)
    fix t K T k assume t: "t \<in> ?GSMP" "Ana t = (K, T)" "k \<in> set K"
    hence "k \<in> GSMP M" using GSMP_Ana_key by blast
    moreover have "\<forall>f \<in> funs_term t. ?P f" using t(1) by auto
    with t(2,3) have "\<forall>f \<in> funs_term k. ?P f"
    proof (induction t arbitrary: k rule: Ana.induct)
      case 1 thus ?case by (metis Ana_Fu_keys_not_pubval_terms surj_pair)
    qed auto
    moreover have "\<forall>f \<in> funs_term t. \<not>is_Abs f" using t(1) by auto
    with t(2,3) have "\<forall>f \<in> funs_term k. \<not>is_Abs f"
    proof (induction t arbitrary: k rule: Ana.induct)
      case 1 thus ?case by (metis Ana_Fu_keys_not_abs_terms surj_pair)
    qed auto
    ultimately show "k \<in> ?GSMP" by simp
  qed

  have "\<langle>IK; M\<rangle> \<turnstile>\<^sub>G\<^sub>S\<^sub>M\<^sub>P t"
    unfolding intruder_deduct_GSMP_def
    by (rule restricted_deduct_if_deduct'[OF 1 2 3 t])
  thus ?thesis
  proof (induction t rule: intruder_deduct_GSMP_induct)
    case (AxiomH t)
    show ?case using IK(2) abs_in[OF AxiomH.hyps] by force
  next
    case (ComposeH T f)
    have *: "Fun f T \<cdot>\<^sub>\<alpha> \<alpha> = Fun f (map (\<lambda>t. t \<cdot>\<^sub>\<alpha> \<alpha>) T)"
      using ComposeH.hyps(2,4)
      by (cases f) auto

    have **: "length (map (\<lambda>t. t \<cdot>\<^sub>\<alpha> \<alpha>) T) = arity f"
      using ComposeH.hyps(1)
      by auto

    show ?case
      using intruder_deduct.Compose[OF ** ComposeH.hyps(2)] ComposeH.IH(1) *
      by auto
  next
    case (DecomposeH t K T' t\<^sub>i)
    have *: "Ana (t \<cdot>\<^sub>\<alpha> \<alpha>) = (K \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>, T' \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>)"
      using Ana_abs[OF DecomposeH.hyps(2)]
      by metis

    have **: "t\<^sub>i \<cdot>\<^sub>\<alpha> \<alpha> \<in> set (T' \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>)"
      using DecomposeH.hyps(4) abs_in abs_list_set_is_set_abs_set[of T']
      by auto

    have ***: "FP \<turnstile> k"
      when k: "k \<in> set (K \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>)" for k
    proof -
      obtain k' where k': "k' \<in> set K" "k = k' \<cdot>\<^sub>\<alpha> \<alpha>"
        by (metis (no_types) k abs_apply_terms_def imageE abs_list_set_is_set_abs_set)

      show "FP \<turnstile> k"
        using DecomposeH.IH k' by blast
    qed

    show ?case
      using intruder_deduct.Decompose[OF _ * _ **]
            DecomposeH.IH(1) ***(1)
      by blast
  qed
qed

end


subsection \<open>Computing and Checking Term Implications and Messages\<close>
context stateful_protocol_model
begin

abbreviation (input) "absc s \<equiv> (Fun (Abs s) []::('fun,'atom,'sets,'lbl) prot_term)"

fun absdbupd where
  "absdbupd [] _ a = a"
| "absdbupd (insert\<langle>Var y, Fun (Set s) T\<rangle>#D) x a = (
    if x = y then absdbupd D x (insert s a) else absdbupd D x a)"
| "absdbupd (delete\<langle>Var y, Fun (Set s) T\<rangle>#D) x a = (
    if x = y then absdbupd D x (a - {s}) else absdbupd D x a)"
| "absdbupd (_#D) x a = absdbupd D x a"

lemma absdbupd_cons_cases:
  "absdbupd (insert\<langle>Var x, Fun (Set s) T\<rangle>#D) x d = absdbupd D x (insert s d)"
  "absdbupd (delete\<langle>Var x, Fun (Set s) T\<rangle>#D) x d = absdbupd D x (d - {s})"
  "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T) \<Longrightarrow> absdbupd (insert\<langle>t,u\<rangle>#D) x d = absdbupd D x d"
  "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T) \<Longrightarrow> absdbupd (delete\<langle>t,u\<rangle>#D) x d = absdbupd D x d"
proof -
  assume *: "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T)"
  let ?P = "absdbupd (insert\<langle>t,u\<rangle>#D) x d = absdbupd D x d"
  let ?Q = "absdbupd (delete\<langle>t,u\<rangle>#D) x d = absdbupd D x d"
  { fix y f T assume "t = Fun f T \<or> u = Var y" hence ?P ?Q by auto
  } moreover {
    fix y f T assume "t = Var y" "u = Fun f T" hence ?P using * by (cases f) auto
  } moreover {
    fix y f T assume "t = Var y" "u = Fun f T" hence ?Q using * by (cases f) auto
  } ultimately show ?P ?Q by (metis term.exhaust)+
qed simp_all

lemma absdbupd_filter: "absdbupd S x d = absdbupd (filter is_Update S) x d"
by (induction S x d rule: absdbupd.induct) simp_all

lemma absdbupd_append:
  "absdbupd (A@B) x d = absdbupd B x (absdbupd A x d)"
proof (induction A arbitrary: d)
  case (Cons a A) thus ?case
  proof (cases a)
    case (Insert t u) thus ?thesis
    proof (cases "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T)")
      case False
      then obtain s T where "t = Var x" "u = Fun (Set s) T" by moura
      thus ?thesis by (simp add: Insert Cons.IH absdbupd_cons_cases(1))
    qed (simp_all add: Cons.IH absdbupd_cons_cases(3))
  next
    case (Delete t u) thus ?thesis
    proof (cases "t \<noteq> Var x \<or> (\<nexists>s T. u = Fun (Set s) T)")
      case False
      then obtain s T where "t = Var x" "u = Fun (Set s) T" by moura
      thus ?thesis by (simp add: Delete Cons.IH absdbupd_cons_cases(2))
    qed (simp_all add: Cons.IH absdbupd_cons_cases(4))
  qed simp_all
qed simp

lemma absdbupd_wellformed_transaction:
  assumes T: "wellformed_transaction T"
  shows "absdbupd (unlabel (transaction_strand T)) = absdbupd (unlabel (transaction_updates T))"
proof -
  define S0 where "S0 \<equiv> unlabel (transaction_strand T)"
  define S1 where "S1 \<equiv> unlabel (transaction_receive T)"
  define S2 where "S2 \<equiv> unlabel (transaction_checks T)"
  define S3 where "S3 \<equiv> unlabel (transaction_updates T)"
  define S4 where "S4 \<equiv> unlabel (transaction_send T)"

  note S_defs = S0_def S1_def S2_def S3_def S4_def

  have 0: "list_all is_Receive S1"
          "list_all is_Check_or_Assignment S2"
          "list_all is_Update S3"
          "list_all is_Send S4"
    using T unfolding wellformed_transaction_def S_defs by metis+

  have "filter is_Update S1 = []"
       "filter is_Update S2 = []"
       "filter is_Update S3 = S3"
       "filter is_Update S4 = []"
    using list_all_filter_nil[OF 0(1), of is_Update]
          list_all_filter_nil[OF 0(2), of is_Update]
          list_all_filter_eq[OF 0(3)]
          list_all_filter_nil[OF 0(4), of is_Update]
    by blast+
  moreover have "S0 = S1@S2@S3@S4"
    unfolding S_defs transaction_strand_def unlabel_def by auto
  ultimately have "filter is_Update S0 = S3"
    using filter_append[of is_Update] list_all_append[of is_Update]
    by simp
  thus ?thesis
    using absdbupd_filter[of S0]
    unfolding S_defs by presburger
qed

fun abs_substs_set::
  "[('fun,'atom,'sets,'lbl) prot_var list,
    'sets set list,
    ('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set,
    ('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set,
    ('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set \<Rightarrow> bool]
  \<Rightarrow> ((('fun,'atom,'sets,'lbl) prot_var \<times> 'sets set) list) list"
where
  "abs_substs_set [] _ _ _ _ = [[]]"
| "abs_substs_set (x#xs) as posconstrs negconstrs msgconstrs = (
    let bs = filter (\<lambda>a. posconstrs x \<subseteq> a \<and> a \<inter> negconstrs x = {} \<and> msgconstrs x a) as;
        \<Delta> = abs_substs_set xs as posconstrs negconstrs msgconstrs
    in concat (map (\<lambda>b. map (\<lambda>\<delta>. (x, b)#\<delta>) \<Delta>) bs))"

definition abs_substs_fun::
  "[(('fun,'atom,'sets,'lbl) prot_var \<times> 'sets set) list,
    ('fun,'atom,'sets,'lbl) prot_var]
  \<Rightarrow> 'sets set"
where
  "abs_substs_fun \<delta> x = (case find (\<lambda>b. fst b = x) \<delta> of Some (_,a) \<Rightarrow> a | None \<Rightarrow> {})"

lemmas abs_substs_set_induct = abs_substs_set.induct[case_names Nil Cons]

fun transaction_poschecks_comp::
  "(('fun,'atom,'sets,'lbl) prot_fun, ('fun,'atom,'sets,'lbl) prot_var) stateful_strand
  \<Rightarrow> (('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set)"
where
  "transaction_poschecks_comp [] = (\<lambda>_. {})"
| "transaction_poschecks_comp (\<langle>_: Var x \<in> Fun (Set s) []\<rangle>#T) = (
    let f = transaction_poschecks_comp T in f(x := insert s (f x)))"
| "transaction_poschecks_comp (_#T) = transaction_poschecks_comp T"

fun transaction_negchecks_comp::
  "(('fun,'atom,'sets,'lbl) prot_fun, ('fun,'atom,'sets,'lbl) prot_var) stateful_strand
  \<Rightarrow> (('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set)"
where
  "transaction_negchecks_comp [] = (\<lambda>_. {})"
| "transaction_negchecks_comp (\<langle>Var x not in Fun (Set s) []\<rangle>#T) = (
    let f = transaction_negchecks_comp T in f(x := insert s (f x)))"
| "transaction_negchecks_comp (_#T) = transaction_negchecks_comp T"

definition transaction_check_pre where
  "transaction_check_pre FPT T \<delta> \<equiv>
    let (FP, _, TI) = FPT;
        C = set (unlabel (transaction_checks T));
        xs = fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T));
        \<theta> = \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x
    in (\<forall>x \<in> set (transaction_fresh T). \<delta> x = {}) \<and>
       (\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<delta>)) \<and>
       (\<forall>u \<in> C.
          (is_InSet u \<longrightarrow> (
            let x = the_elem_term u; s = the_set_term u
            in (is_Var x \<and> is_Fun_Set s) \<longrightarrow> the_Set (the_Fun s) \<in> \<delta> (the_Var x))) \<and>
          ((is_NegChecks u \<and> bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p u = [] \<and> the_eqs u = [] \<and> length (the_ins u) = 1) \<longrightarrow> (
            let x = fst (hd (the_ins u)); s = snd (hd (the_ins u))
            in (is_Var x \<and> is_Fun_Set s) \<longrightarrow> the_Set (the_Fun s) \<notin> \<delta> (the_Var x))))"

definition transaction_check_post where
  "transaction_check_post FPT T \<delta> \<equiv>
    let (FP, _, TI) = FPT;
        xs = fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T));
        \<theta> = \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x;
        u = \<lambda>\<delta> x. absdbupd (unlabel (transaction_updates T)) x (\<delta> x)
    in (\<forall>x \<in> set xs - set (transaction_fresh T). \<delta> x \<noteq> u \<delta> x \<longrightarrow> List.member TI (\<delta> x, u \<delta> x)) \<and>
       (\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> (u \<delta>)))"

definition fun_point_inter where "fun_point_inter f g \<equiv> \<lambda>x. f x \<inter> g x"
definition fun_point_union where "fun_point_union f g \<equiv> \<lambda>x. f x \<union> g x"
definition fun_point_Inter where "fun_point_Inter fs \<equiv> \<lambda>x. \<Inter>f \<in> fs. f x"
definition fun_point_Union where "fun_point_Union fs \<equiv> \<lambda>x. \<Union>f \<in> fs. f x"
definition fun_point_Inter_list where "fun_point_Inter_list fs \<equiv> \<lambda>x. \<Inter>(set (map (\<lambda>f. f x) fs))"
definition fun_point_Union_list where "fun_point_Union_list fs \<equiv> \<lambda>x. \<Union>(set (map (\<lambda>f. f x) fs))"
definition ticl_abs where "ticl_abs TI a \<equiv> set (a#map snd (filter (\<lambda>p. fst p = a) TI))"
definition ticl_abss where "ticl_abss TI as \<equiv> \<Union>a \<in> as. ticl_abs TI a"

lemma fun_point_Inter_set_eq:
  "fun_point_Inter (set fs) = fun_point_Inter_list fs"
unfolding fun_point_Inter_def fun_point_Inter_list_def by simp

lemma fun_point_Union_set_eq:
  "fun_point_Union (set fs) = fun_point_Union_list fs"
unfolding fun_point_Union_def fun_point_Union_list_def by simp

lemma ticl_abs_refl_in: "x \<in> ticl_abs TI x"
unfolding ticl_abs_def by simp

lemma ticl_abs_iff:
  assumes TI: "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
  shows "ticl_abs TI a = {b. (a,b) \<in> (set TI)\<^sup>*}"  
proof (intro order_antisym subsetI)
  fix x assume x: "x \<in> {b. (a, b) \<in> (set TI)\<^sup>*}"
  hence "x = a \<or> (x \<noteq> a \<and> (a,x) \<in> (set TI)\<^sup>+)" by (metis mem_Collect_eq rtranclD)
  moreover have "ticl_abs TI a = {a} \<union> {b. (a,b) \<in> set TI}" unfolding ticl_abs_def by force
  ultimately show "x \<in> ticl_abs TI a" using TI by blast
qed (fastforce simp add: ticl_abs_def)

lemma ticl_abs_Inter:
  assumes xs: "\<Inter>(ticl_abs TI ` xs) \<noteq> {}"
    and TI: "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
  shows "\<Inter>(ticl_abs TI ` \<Inter>(ticl_abs TI ` xs)) \<subseteq> \<Inter>(ticl_abs TI ` xs)"
proof
  fix x assume x: "x \<in> \<Inter>(ticl_abs TI ` \<Inter>(ticl_abs TI ` xs))"
  have *: "\<Inter>(ticl_abs TI ` xs) = {b. \<forall>a \<in> xs. (a,b) \<in> (set TI)\<^sup>*}"
    unfolding ticl_abs_iff[OF TI] by blast

  have "(b,x) \<in> (set TI)\<^sup>*" when b: "\<forall>a \<in> xs. (a,b) \<in> (set TI)\<^sup>*" for b
    using x b unfolding ticl_abs_iff[OF TI] by blast
  hence "(a,x) \<in> (set TI)\<^sup>*" when "a \<in> xs" for a
    using that xs rtrancl.rtrancl_into_rtrancl[of a _ "(set TI)\<^sup>*" x]
    unfolding * rtrancl_idemp[of "set TI"] by blast
  thus "x \<in> \<Inter>(ticl_abs TI ` xs)" unfolding * by blast
qed

function (sequential) match_abss'
::"(('a,'b,'c,'d) prot_fun, 'e) term \<Rightarrow>
   (('a,'b,'c,'d) prot_fun, 'e) term \<Rightarrow>
   ('e \<Rightarrow> 'c set set) option"
where
  "match_abss' (Var x) (Fun (Abs a) _) = Some ((\<lambda>_. {})(x := {a}))"
| "match_abss' (Fun f ts) (Fun g ss) = (
    if f = g \<and> length ts = length ss
    then map_option fun_point_Union_list (those (map2 match_abss' ts ss))
    else None)"
| "match_abss' _ _ = None"
by pat_completeness auto
termination
proof -
  let ?m = "measures [size \<circ> fst]"

  have 0: "wf ?m" by simp

  show ?thesis
    apply (standard, use 0 in fast)
    by (metis (no_types) comp_def fst_conv measures_less Fun_zip_size_lt(1))
qed

definition match_abss where
  "match_abss OCC TI t s \<equiv> (
    let xs = fv t;
        OCC' = set OCC;
        f = \<lambda>\<delta> x. if x \<in> xs then \<delta> x else OCC';
        g = \<lambda>\<delta> x. \<Inter>(ticl_abs TI ` \<delta> x)
    in case match_abss' t s of
      Some \<delta> \<Rightarrow>
        let \<delta>' = g \<delta>
        in if \<forall>x \<in> xs. \<delta>' x \<noteq> {} then Some (f \<delta>') else None
    | None \<Rightarrow> None)"

lemma match_abss'_Var_inv:
  assumes \<delta>: "match_abss' (Var x) t = Some \<delta>"
  shows "\<exists>a ts. t = Fun (Abs a) ts \<and> \<delta> = (\<lambda>_. {})(x := {a})"
proof -
  obtain f ts where t: "t = Fun f ts" using \<delta> by (cases t) auto
  then obtain a where a: "f = Abs a" using \<delta> by (cases f) auto
  show ?thesis using \<delta> unfolding t a by simp 
qed

lemma match_abss'_Fun_inv:
  assumes "match_abss' (Fun f ts) (Fun g ss) = Some \<delta>"
  shows "f = g" (is ?A)
    and "length ts = length ss" (is ?B)
    and "\<exists>\<theta>. Some \<theta> = those (map2 match_abss' ts ss) \<and> \<delta> = fun_point_Union_list \<theta>" (is ?C)
    and "\<forall>(t,s) \<in> set (zip ts ss). \<exists>\<sigma>. match_abss' t s = Some \<sigma>" (is ?D)
proof -
  note 0 = assms match_abss'.simps(2)[of f ts g ss] option.distinct(1)
  show ?A by (metis 0)
  show ?B by (metis 0)
  show ?C by (metis (no_types, opaque_lifting) 0 map_option_eq_Some)
  thus ?D using map2_those_Some_case[of match_abss' ts ss] by fastforce
qed

lemma match_abss'_FunI:
  assumes \<Delta>: "\<And>i. i < length T \<Longrightarrow> match_abss' (U ! i) (T ! i) = Some (\<Delta> i)"
    and T: "length T = length U"
  shows "match_abss' (Fun f U) (Fun f T) = Some (fun_point_Union_list (map \<Delta> [0..<length T]))"
proof -
  have "match_abss' (Fun f U) (Fun f T) =
          map_option fun_point_Union_list (those (map2 match_abss' U T))"
    using T match_abss'.simps(2)[of f U f T] by presburger
  moreover have "those (map2 match_abss' U T) = Some (map \<Delta> [0..<length T])"
    using \<Delta> T those_map2_SomeI by metis
  ultimately show ?thesis by simp
qed

lemma match_abss'_Fun_param_subset:
  assumes "match_abss' (Fun f ts) (Fun g ss)  = Some \<delta>"
    and "(t,s) \<in> set (zip ts ss)"
    and "match_abss' t s = Some \<sigma>"
  shows "\<sigma> x \<subseteq> \<delta> x"
proof -
  obtain \<theta> where \<theta>:
      "those (map2 match_abss' ts ss) = Some \<theta>"
      "\<delta> = fun_point_Union_list \<theta>"
    using match_abss'_Fun_inv[OF assms(1)] by metis

  have "\<sigma> \<in> set \<theta>" using \<theta>(1) assms(2-) those_Some_iff[of "map2 match_abss' ts ss" \<theta>] by force
  thus ?thesis using \<theta>(2) unfolding fun_point_Union_list_def by auto
qed

lemma match_abss'_fv_is_nonempty:
  assumes "match_abss' t s = Some \<delta>"
    and "x \<in> fv t"
  shows "\<delta> x \<noteq> {}" (is "?P \<delta>")
using assms
proof (induction t s arbitrary: \<delta> rule: match_abss'.induct)
  case (2 f ts g ss)
  note prems = "2.prems"
  note IH = "2.IH"

  have 0: "\<forall>(t,s) \<in> set (zip ts ss). \<exists>\<sigma>. match_abss' t s = Some \<sigma>" "f = g" "length ts = length ss"
    using match_abss'_Fun_inv[OF prems(1)] by simp_all

  obtain t where t: "t \<in> set ts" "x \<in> fv t" using prems(2) by auto
  then obtain s where s: "s \<in> set ss" "(t,s) \<in> set (zip ts ss)"
    by (meson 0(3) in_set_impl_in_set_zip1 in_set_zipE)
  then obtain \<sigma> where \<sigma>: "match_abss' t s = Some \<sigma>" using 0(1) by fast

  show ?case
    using IH[OF conjI[OF 0(2,3)] s(2) _ \<sigma>] t(2) match_abss'_Fun_param_subset[OF prems(1) s(2) \<sigma>]
    by auto
qed auto

lemma match_abss'_nonempty_is_fv:
  fixes s t::"(('a,'b,'c,'d) prot_fun, 'v) term"
  assumes "match_abss' s t = Some \<delta>"
    and "\<delta> x \<noteq> {}"
  shows "x \<in> fv s"
using assms
proof (induction s t arbitrary: \<delta> rule: match_abss'.induct)
  case (2 f ts g ss)
  note prems = "2.prems"
  note IH = "2.IH"

  obtain \<theta> where \<theta>: "Some \<theta> = those (map2 match_abss' ts ss)" "\<delta> = fun_point_Union_list \<theta>"
      and fg: "f = g" "length ts = length ss"
    using match_abss'_Fun_inv[OF prems(1)] by fast

  have "\<exists>\<sigma> \<in> set \<theta>. \<sigma> x \<noteq> {}"
    using fg(2) prems \<theta> unfolding fun_point_Union_list_def by auto
  then obtain t' s' \<sigma> where ts':
      "(t',s') \<in> set (zip ts ss)" "match_abss' t' s' = Some \<sigma>" "\<sigma> x \<noteq> {}"
    using those_map2_SomeD[OF \<theta>(1)[symmetric]] by blast

  show ?case
    using ts'(3) IH[OF conjI[OF fg] ts'(1) _ ts'(2)] set_zip_leftD[OF ts'(1)] by force
qed auto

lemma match_abss'_Abs_in_funs_term:
  fixes s t::"(('a,'b,'c,'d) prot_fun, 'v) term"
  assumes "match_abss' s t = Some \<delta>"
    and "a \<in> \<delta> x"
  shows "Abs a \<in> funs_term t"
using assms
proof (induction s t arbitrary: a \<delta> rule: match_abss'.induct)
  case (1 y b ts) show ?case
    using match_abss'_Var_inv[OF "1.prems"(1)]  "1.prems"(2)
    by (cases "x = y") simp_all
next
  case (2 f ts g ss)
  note prems = "2.prems"
  note IH = "2.IH"

  obtain \<theta> where \<theta>: "Some \<theta> = those (map2 match_abss' ts ss)" "\<delta> = fun_point_Union_list \<theta>"
      and fg: "f = g" "length ts = length ss"
    using match_abss'_Fun_inv[OF prems(1)] by fast

  obtain t' s' \<sigma> where ts': "(t',s') \<in> set (zip ts ss)" "match_abss' t' s' = Some \<sigma>" "a \<in> \<sigma> x"
    using fg(2) prems \<theta> those_map2_SomeD[OF \<theta>(1)[symmetric]]
    unfolding fun_point_Union_list_def by fastforce

  show ?case
    using ts'(1) IH[OF conjI[OF fg] ts'(1) _ ts'(2,3)]
    by (meson set_zip_rightD term.set_intros(2))
qed auto

lemma match_abss'_subst_fv_ex_abs:
  assumes "match_abss' s (s \<cdot> \<delta>) = Some \<sigma>"
    and TI: "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
  shows "\<forall>x \<in> fv s. \<exists>a ts. \<delta> x = Fun (Abs a) ts \<and> \<sigma> x = {a}" (is "?P s \<sigma>")
using assms(1)
proof (induction s "s \<cdot> \<delta>" arbitrary: \<sigma> rule: match_abss'.induct)
  case (2 f ts g ss)
  note prems = "2.prems"
  note hyps = "2.hyps"

  obtain \<theta> where \<theta>: "Some \<theta> = those (map2 match_abss' ts ss)" "\<sigma> = fun_point_Union_list \<theta>"
      and fg: "f = g" "length ts = length ss" "ss = ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>"
      and ts: "\<forall>(t,s) \<in> set (zip ts ss). \<exists>\<sigma>. match_abss' t s = Some \<sigma>"
    using match_abss'_Fun_inv[OF prems(1)[unfolded hyps(2)[symmetric]]] hyps(2) by fastforce

  have 0: "those (map (\<lambda>t. match_abss' t (t \<cdot> \<delta>)) ts) = Some \<theta>"
    using \<theta>(1) map2_map_subst unfolding fg(3) by metis

  have 1: "\<forall>t \<in> set ts. \<exists>\<sigma>. match_abss' t (t \<cdot> \<delta>) = Some \<sigma>"
    using ts zip_map_subst[of ts \<delta>] unfolding fg(3) by simp

  have 2: "\<sigma>' \<in> set \<theta>"
    when t: "t \<in> set ts" "match_abss' t (t \<cdot> \<delta>) = Some \<sigma>'" for t \<sigma>'
    using t 0 those_Some_iff[of "map (\<lambda>t. match_abss' t (t \<cdot> \<delta>)) ts" \<theta>] by force

  have 3: "?P t \<sigma>'" "\<sigma>' x \<noteq> {}"
    when t: "t \<in> set ts" "x \<in> fv t" "match_abss' t (t \<cdot> \<delta>) = Some \<sigma>'" for t \<sigma>' x
    using t hyps(1)[OF conjI[OF fg(1,2)], of "(t, t \<cdot> \<delta>)" t \<sigma>'] zip_map_subst[of ts \<delta>]
          match_abss'_fv_is_nonempty[of t "t \<cdot> \<delta>" \<sigma>' x]
    unfolding fg(3) by auto

  have 4: "\<sigma>' x = {}"
    when t: "x \<notin> fv t" "match_abss' t (t \<cdot> \<delta>) = Some \<sigma>'" for t \<sigma>' x
    by (meson t match_abss'_nonempty_is_fv)

  show ?case
  proof
    fix x assume "x \<in> fv (Fun f ts)"
    then obtain t \<sigma>' where t: "t \<in> set ts" "x \<in> fv t" and \<sigma>': "match_abss' t (t \<cdot> \<delta>) = Some \<sigma>'"
      using 1 by auto
    then obtain a tsa where a: "\<delta> x = Fun (Abs a) tsa"
      using 3[OF t \<sigma>'] by fast

    have "\<sigma>'' x = {a} \<or> \<sigma>'' x = {}"
      when "\<sigma>'' \<in> set \<theta>" for \<sigma>''
      using that a 0 3[of _ x] 4[of x]
      unfolding those_Some_iff by fastforce
    thus "\<exists>a ts. \<delta> x = Fun (Abs a) ts \<and> \<sigma> x = {a}"
      using a 2[OF t(1) \<sigma>'] 3[OF t \<sigma>'] unfolding \<theta>(2) fun_point_Union_list_def by auto
  qed
qed auto

lemma match_abss'_subst_disj_nonempty:
  assumes TI: "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and "match_abss' s (s \<cdot> \<delta>) = Some \<sigma>"
    and "x \<in> fv s"
  shows "\<Inter>(ticl_abs TI ` \<sigma> x) \<noteq> {} \<and> (\<exists>a tsa. \<delta> x = Fun (Abs a) tsa \<and> \<sigma> x = {a})" (is "?P \<sigma>")
using assms(2,3)
proof (induction s "s \<cdot> \<delta>" arbitrary: \<sigma> rule: match_abss'.induct)
  case (1 x a ts) thus ?case unfolding ticl_abs_def by force
next
  case (2 f ts g ss)
  note prems = "2.prems"
  note hyps = "2.hyps"

  obtain \<theta> where \<theta>: "Some \<theta> = those (map2 match_abss' ts ss)" "\<sigma> = fun_point_Union_list \<theta>"
      and fg: "f = g" "length ts = length ss" "ss = ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>"
      and ts: "\<forall>(t,s) \<in> set (zip ts ss). \<exists>\<sigma>. match_abss' t s = Some \<sigma>"
    using match_abss'_Fun_inv[OF prems(1)[unfolded hyps(2)[symmetric]]] hyps(2) by fastforce

  define ts' where "ts' \<equiv> filter (\<lambda>t. x \<in> fv t) ts"
  define \<theta>' where "\<theta>' \<equiv> map (\<lambda>t. (t, the (match_abss' t (t \<cdot> \<delta>)))) ts"
  define \<theta>'' where "\<theta>'' \<equiv> map (\<lambda>t. the (match_abss' t (t \<cdot> \<delta>))) ts'"

  have 0: "those (map (\<lambda>t. match_abss' t (t \<cdot> \<delta>)) ts) = Some \<theta>"
    using \<theta>(1) map2_map_subst unfolding fg(3) by metis

  have 1: "\<forall>t \<in> set ts. \<exists>\<sigma>. match_abss' t (t \<cdot> \<delta>) = Some \<sigma>"
    using ts zip_map_subst[of ts \<delta>] unfolding fg(3) by simp

  have ts_not_nil: "ts \<noteq> []"
    using prems(2) by fastforce
  hence "\<exists>t \<in> set ts. x \<in> fv t" using prems(2) by simp
  then obtain a tsa where a: "\<delta> x = Fun (Abs a) tsa" 
    using 1 match_abss'_subst_fv_ex_abs[OF _ TI, of _ \<delta>]
    by metis
  hence a': "\<sigma>' x = {a}"
    when "t \<in> set ts" "x \<in> fv t" "match_abss' t (t \<cdot> \<delta>) = Some \<sigma>'"
    for t \<sigma>'
    using that match_abss'_subst_fv_ex_abs[OF _ TI, of _ \<delta>]
    by fastforce

  have "ts' \<noteq> []" using prems(2) unfolding ts'_def by (simp add: filter_empty_conv) 
  hence \<theta>''_not_nil: "\<theta>'' \<noteq> []" unfolding \<theta>''_def by simp

  have 2: "\<sigma>' \<in> set \<theta>"
    when t: "t \<in> set ts" "match_abss' t (t \<cdot> \<delta>) = Some \<sigma>'" for t \<sigma>'
    using t 0 those_Some_iff[of "map (\<lambda>t. match_abss' t (t \<cdot> \<delta>)) ts" \<theta>] by force

  have 3: "?P \<sigma>'" "\<sigma>' x \<noteq> {}"
    when t: "t \<in> set ts'" "match_abss' t (t \<cdot> \<delta>) = Some \<sigma>'" for t \<sigma>'
    using t hyps(1)[OF conjI[OF fg(1,2)], of "(t, t \<cdot> \<delta>)" t \<sigma>'] zip_map_subst[of ts \<delta>]
          match_abss'_fv_is_nonempty[of t "t \<cdot> \<delta>" \<sigma>' x]
    unfolding fg(3) ts'_def by (force, force)

  have 4: "\<sigma>' x = {}"
    when t: "x \<notin> fv t" "match_abss' t (t \<cdot> \<delta>) = Some \<sigma>'" for t \<sigma>'
    by (meson t match_abss'_nonempty_is_fv)

  have 5: "\<theta> = map snd \<theta>'"
    using 0 1 unfolding \<theta>'_def by (induct ts arbitrary: \<theta>) auto

  have "fun_point_Union_list (map snd \<theta>') x =
        fun_point_Union_list (map snd (filter (\<lambda>(t,_). x \<in> fv t) \<theta>')) x"
    using 1 4 unfolding \<theta>'_def fun_point_Union_list_def by fastforce
  hence 6: "fun_point_Union_list \<theta> x = fun_point_Union_list \<theta>'' x"
    using 0 1 4 unfolding 5 \<theta>'_def \<theta>''_def fun_point_Union_list_def ts'_def by auto

  have 7: "?P \<sigma>'" "\<sigma>' x \<noteq> {}"
    when \<sigma>': "\<sigma>' \<in> set \<theta>''" for \<sigma>'
    using that 1 3 unfolding \<theta>''_def ts'_def by auto

  have "\<sigma>' x = {a}"
    when \<sigma>': "\<sigma>' \<in> set \<theta>''" for \<sigma>'
    using \<sigma>' a' 1 unfolding \<theta>''_def ts'_def by fastforce
  hence "fun_point_Union_list \<theta>'' x = {b | b \<sigma>'. \<sigma>' \<in> set \<theta>'' \<and> b \<in> {a}}"
    using \<theta>''_not_nil unfolding fun_point_Union_list_def by auto
  hence 8: "fun_point_Union_list \<theta>'' x = {a}"
    using \<theta>''_not_nil by auto

  show ?case
    using 8 a
    unfolding \<theta>(2) 6 ticl_abs_iff[OF TI] by auto
qed simp_all

lemma match_abssD:
  fixes OCC TI s
  defines "f \<equiv> (\<lambda>\<delta> x. if x \<in> fv s then \<delta> x else set OCC)"
    and "g \<equiv> (\<lambda>\<delta> x. \<Inter>(ticl_abs TI ` \<delta> x))"
  assumes \<delta>': "match_abss OCC TI s t = Some \<delta>'" 
  shows "\<exists>\<delta>. match_abss' s t = Some \<delta> \<and> \<delta>' = f (g \<delta>) \<and> (\<forall>x \<in> fv s. \<delta> x \<noteq> {} \<and> f (g \<delta>) x \<noteq> {}) \<and>
             (set OCC \<noteq> {} \<longrightarrow> (\<forall>x. f (g \<delta>) x \<noteq> {}))"
proof -
  obtain \<delta> where \<delta>: "match_abss' s t = Some \<delta>"
    using \<delta>' unfolding match_abss_def by force
  hence "Some \<delta>' = (if \<forall>x \<in> fv s. g \<delta> x \<noteq> {} then Some (f (g \<delta>)) else None)"
    using \<delta>' unfolding match_abss_def f_def g_def Let_def by simp
  hence "\<delta>' = f (g \<delta>)" "\<forall>x \<in> fv s. \<delta> x \<noteq> {} \<and> f (g \<delta>) x \<noteq> {}"
    by (metis (no_types, lifting) option.inject option.distinct(1),
        metis (no_types, lifting) f_def option.distinct(1) match_abss'_fv_is_nonempty[OF \<delta>])
  thus ?thesis using \<delta> unfolding f_def by force
qed

lemma match_abss_ticl_abs_Inter_subset:
  assumes TI: "set TI = {(a,b). (a,b) \<in> (set TI)\<^sup>+ \<and> a \<noteq> b}"
    and \<delta>: "match_abss OCC TI s t = Some \<delta>"
    and x: "x \<in> fv s"
  shows "\<Inter>(ticl_abs TI ` \<delta> x) \<subseteq> \<delta> x"
proof -
  let ?h1 = "\<lambda>\<delta> x. if x \<in> fv s then \<delta> x else set OCC"
  let ?h2 = "\<lambda>\<delta> x. \<Inter>(ticl_abs TI ` \<delta> x)"

  obtain \<delta>' where \<delta>':
      "match_abss' s t = Some \<delta>'" "\<delta> = ?h1 (?h2 \<delta>')"
      "\<forall>x \<in> fv s. \<delta>' x \<noteq> {} \<and> \<delta> x \<noteq> {}"
    using match_abssD[OF \<delta>] by blast

  have "\<delta> x = \<Inter>(ticl_abs TI ` \<delta>' x)" "\<delta>' x \<noteq> {}" "\<delta> x \<noteq> {}"
    using x \<delta>'(2,3) by auto
  thus ?thesis
    using ticl_abs_Inter TI by simp
qed

lemma match_abss_fv_has_abs:
  assumes "match_abss OCC TI s t = Some \<delta>"
    and "x \<in> fv s"
  shows "\<delta> x \<noteq> {}"
using assms match_abssD by fast

lemma match_abss_OCC_if_not_fv:
  fixes s t::"(('a,'b,'c,'d) prot_fun, 'v) term"
  assumes \<delta>': "match_abss OCC TI s t = Some \<delta>'"
    and x: "\<delta>' x \<noteq> {}" "x \<notin> fv s"
  shows "\<delta>' x = set OCC"
proof -
  define f where "f \<equiv> \<lambda>s::(('a,'b,'c,'d) prot_fun, 'v) term. \<lambda>\<delta> x. if x \<in> fv s then \<delta> x else set OCC"
  define g where "g \<equiv> \<lambda>\<delta>. \<lambda>x::'v. \<Inter>(ticl_abs TI ` \<delta> x)"

  obtain \<delta> where "match_abss' s t = Some \<delta>" "\<delta>' = f s (g \<delta>)"
    using match_abssD[OF \<delta>'] unfolding f_def g_def by blast
  thus ?thesis
    using x match_abss'_nonempty_is_fv unfolding f_def by presburger
qed

inductive synth_abs_substs_constrs_rel for FP OCC TI where
  SolveNil:
    "synth_abs_substs_constrs_rel FP OCC TI [] (\<lambda>_. set OCC)"
| SolveCons:
    "ts \<noteq> [] \<Longrightarrow> \<forall>t \<in> set ts. synth_abs_substs_constrs_rel FP OCC TI [t] (\<theta> t)
      \<Longrightarrow> synth_abs_substs_constrs_rel FP OCC TI ts (fun_point_Inter (\<theta> ` set ts))"
| SolvePubConst:
    "arity c = 0 \<Longrightarrow> public c
      \<Longrightarrow> synth_abs_substs_constrs_rel FP OCC TI [Fun c []] (\<lambda>_. set OCC)"
| SolvePrivConstIn:
    "arity c = 0 \<Longrightarrow> \<not>public c \<Longrightarrow> Fun c [] \<in> set FP
      \<Longrightarrow> synth_abs_substs_constrs_rel FP OCC TI [Fun c []] (\<lambda>_. set OCC)"
| SolvePrivConstNotin:
    "arity c = 0 \<Longrightarrow> \<not>public c \<Longrightarrow> Fun c [] \<notin> set FP
      \<Longrightarrow> synth_abs_substs_constrs_rel FP OCC TI [Fun c []] (\<lambda>_. {})"
| SolveValueVar:
    "\<theta> = ((\<lambda>_. set OCC)(x := ticl_abss TI {a \<in> set OCC. \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s \<in> set FP}))
      \<Longrightarrow> synth_abs_substs_constrs_rel FP OCC TI [Var x] \<theta>"
| SolveComposed:
    "arity f > 0 \<Longrightarrow> length ts = arity f
      \<Longrightarrow> \<forall>\<delta>. \<delta> \<in> \<Delta> \<longleftrightarrow> (\<exists>s \<in> set FP. match_abss OCC TI (Fun f ts) s = Some \<delta>)
      \<Longrightarrow> \<Theta> = (\<lambda>\<delta> x. if \<delta> x \<noteq> {} then \<delta> x else set OCC)
      \<Longrightarrow> \<theta>1 = fun_point_Union (\<Theta> ` \<Delta>)
      \<Longrightarrow> synth_abs_substs_constrs_rel FP OCC TI ts \<theta>2
      \<Longrightarrow> synth_abs_substs_constrs_rel FP OCC TI [Fun f ts] (fun_point_union \<theta>1 \<theta>2)"

fun synth_abs_substs_constrs_aux where
  "synth_abs_substs_constrs_aux FP OCC TI (Var x) = (
    (\<lambda>_. set OCC)(x := ticl_abss TI (set (filter (\<lambda>a. \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s \<in> set FP) OCC))))"
| "synth_abs_substs_constrs_aux FP OCC TI (Fun f ts) = (
    if ts = []
    then if \<not>public f \<and> Fun f ts \<notin> set FP then (\<lambda>_. {}) else (\<lambda>_. set OCC)
    else let \<Delta> = map the (filter (\<lambda>\<delta>. \<delta> \<noteq> None) (map (match_abss OCC TI (Fun f ts)) FP));
             \<Theta> = \<lambda>\<delta> x. let as = \<delta> x in if as \<noteq> {} then as else set OCC;
             \<theta>1 = fun_point_Union_list (map \<Theta> \<Delta>);
             \<theta>2 = fun_point_Inter_list (map (synth_abs_substs_constrs_aux FP OCC TI) ts)
         in fun_point_union \<theta>1 \<theta>2)"

definition synth_abs_substs_constrs where
  "synth_abs_substs_constrs FPT T \<equiv>
    let (FP,OCC,TI) = FPT;
        ts = trms_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_receive T));
        f = fun_point_Inter_list \<circ> map (synth_abs_substs_constrs_aux FP OCC TI)
    in if ts = [] then (\<lambda>_. set OCC) else f ts"

(* definition synth_abs_substs_constrs where
  "synth_abs_substs_constrs FPT T \<equiv>
    let (FP,OCC,TI) = FPT;
        negsy = Not \<circ> intruder_synth_mod_timpls FP TI;
        \<Theta> = \<lambda>\<delta> x. let as = \<delta> x in if as \<noteq> {} then as else set OCC;
        C = unlabel (transaction_checks T);
        poss = transaction_poschecks_comp C;
        negs = transaction_negchecks_comp C;
        ts = trms_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_receive T));
        f = \<lambda>t. let \<Delta> = map the (filter (\<lambda>\<delta>. \<delta> \<noteq> None) (map (match_abss OCC TI t) FP))
                in fun_point_Union_list (map \<Theta> \<Delta>);
        g = \<lambda>t. if is_Fun t \<and> args t \<noteq> []
                then let s = hd (args t)
                in case fv_list s of
                   [] \<Rightarrow> if negsy s then Some (f t) else None
                 | [x] \<Rightarrow> let bs = filter (\<lambda>a. poss x \<subseteq> a \<and> a \<inter> negs x = {}) OCC
                          in if list_all (\<lambda>b. negsy (s \<cdot> Var(x := \<langle>b\<rangle>\<^sub>a\<^sub>b\<^sub>s))) bs
                             then Some (f t) else None
                 | _ \<Rightarrow> None
                else None;
        h = \<lambda>t. case g t of Some d \<Rightarrow> d | None \<Rightarrow> synth_abs_substs_constrs_aux FP OCC TI t
    in if ts = [] then (\<lambda>_. set OCC) else fun_point_Inter_list (map h ts)" *)
(*
poss = transaction_poschecks_comp (C A);
      negs = transaction_negchecks_comp (C A);
      bs = filter (\<lambda>a. poss PK \<subseteq> a \<and> a \<inter> negs PK = {}) OCC
    in if list_all (Not \<circ> sy \<circ> s A) bs
       then Some (map the (filter (\<lambda>\<delta>. \<delta> \<noteq> None) (map (match_abss OCC TI (t' A)) FP)))
       else None
*)
definition transaction_check_comp::
  "[('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set \<Rightarrow> bool,
    ('fun,'atom,'sets,'lbl) prot_term list \<times>
    'sets set list \<times>
    ('sets set \<times> 'sets set) list,
    ('fun,'atom,'sets,'lbl) prot_transaction]
  \<Rightarrow> ((('fun,'atom,'sets,'lbl) prot_var \<times> 'sets set) list) list"
where
  "transaction_check_comp msgcs FPT T \<equiv>
    let (_, OCC, _) = FPT;
        S = unlabel (transaction_strand T);
        C = unlabel (transaction_checks T);
        xs = filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) (fv_list\<^sub>s\<^sub>s\<^sub>t S);
        posconstrs = transaction_poschecks_comp C;
        negconstrs = transaction_negchecks_comp C;
        pre_check = transaction_check_pre FPT T;
        \<Delta> = abs_substs_set xs OCC posconstrs negconstrs msgcs
    in filter (\<lambda>\<delta>. pre_check (abs_substs_fun \<delta>)) \<Delta>"

definition transaction_check'::
  "[('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set \<Rightarrow> bool,
    ('fun,'atom,'sets,'lbl) prot_term list \<times>
    'sets set list \<times>
    ('sets set \<times> 'sets set) list,
    ('fun,'atom,'sets,'lbl) prot_transaction]
  \<Rightarrow> bool"
where
  "transaction_check' msgcs FPT T \<equiv>
    list_all (\<lambda>\<delta>. transaction_check_post FPT T (abs_substs_fun \<delta>))
             (transaction_check_comp msgcs FPT T)"

definition transaction_check::
  "[('fun,'atom,'sets,'lbl) prot_term list \<times>
    'sets set list \<times>
    ('sets set \<times> 'sets set) list,
    ('fun,'atom,'sets,'lbl) prot_transaction]
  \<Rightarrow> bool"
where
  "transaction_check \<equiv> transaction_check' (\<lambda>_ _. True)"

definition transaction_check_alt1::
  "[('fun,'atom,'sets,'lbl) prot_term list \<times>
    'sets set list \<times>
    ('sets set \<times> 'sets set) list,
    ('fun,'atom,'sets,'lbl) prot_transaction]
  \<Rightarrow> bool"
where
  "transaction_check_alt1 FPT T \<equiv>
    let msgcs = synth_abs_substs_constrs FPT T
    in transaction_check' (\<lambda>x a. a \<in> msgcs x) FPT T"

lemma abs_subst_fun_cons:
  "abs_substs_fun ((x,b)#\<delta>) = (abs_substs_fun \<delta>)(x := b)"
unfolding abs_substs_fun_def by fastforce

lemma abs_substs_cons:
  assumes "\<delta> \<in> set (abs_substs_set xs as poss negs msgcs)"
          "b \<in> set as" "poss x \<subseteq> b" "b \<inter> negs x = {}" "msgcs x b"
  shows "(x,b)#\<delta> \<in> set (abs_substs_set (x#xs) as poss negs msgcs)"
using assms by auto

lemma abs_substs_cons':
  assumes \<delta>: "\<delta> \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs msgcs)"
    and b: "b \<in> set as" "poss x \<subseteq> b" "b \<inter> negs x = {}" "msgcs x b"
  shows "\<delta>(x := b) \<in> abs_substs_fun ` set (abs_substs_set (x#xs) as poss negs msgcs)"
proof -
  obtain \<theta> where \<theta>: "\<delta> = abs_substs_fun \<theta>" "\<theta> \<in> set (abs_substs_set xs as poss negs msgcs)"
    using \<delta> by moura
  have "abs_substs_fun ((x, b)#\<theta>) \<in> abs_substs_fun ` set (abs_substs_set (x#xs) as poss negs msgcs)"
    using abs_substs_cons[OF \<theta>(2) b] by blast
  thus ?thesis
    using \<theta>(1) abs_subst_fun_cons[of x b \<theta>] by argo
qed

lemma abs_substs_has_abs:
  assumes "\<forall>x. x \<in> set xs \<longrightarrow> \<delta> x \<in> set as"
    and "\<forall>x. x \<in> set xs \<longrightarrow> poss x \<subseteq> \<delta> x"
    and "\<forall>x. x \<in> set xs \<longrightarrow> \<delta> x \<inter> negs x = {}"
    and "\<forall>x. x \<in> set xs \<longrightarrow> msgcs x (\<delta> x)"
    and "\<forall>x. x \<notin> set xs \<longrightarrow> \<delta> x = {}"
  shows "\<delta> \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs msgcs)"
using assms
proof (induction xs arbitrary: \<delta>)
  case (Cons x xs)
  define \<theta> where "\<theta> \<equiv> \<lambda>y. if y \<in> set xs then \<delta> y else {}"

  have "\<theta> \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs msgcs)"
    using Cons.prems Cons.IH by (simp add: \<theta>_def)
  moreover have "\<delta> x \<in> set as" "poss x \<subseteq> \<delta> x" "\<delta> x \<inter> negs x = {}" "msgcs x (\<delta> x)"
    by (simp_all add: Cons.prems(1,2,3,4))
  ultimately have 0: "\<theta>(x := \<delta> x) \<in> abs_substs_fun ` set (abs_substs_set (x#xs) as poss negs msgcs)"
    by (metis abs_substs_cons')

  have "\<delta> = \<theta>(x := \<delta> x)"
  proof
    fix y show "\<delta> y = (\<theta>(x := \<delta> x)) y"
    proof (cases "y \<in> set (x#xs)")
      case False thus ?thesis using Cons.prems(5) by (fastforce simp add: \<theta>_def)
    qed (auto simp add: \<theta>_def)
  qed
  thus ?case by (metis 0)
qed (auto simp add: abs_substs_fun_def)

lemma abs_substs_abss_bounded:
  assumes "\<delta> \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs msgcs)"
    and "x \<in> set xs"
  shows "\<delta> x \<in> set as"
    and "poss x \<subseteq> \<delta> x"
    and "\<delta> x \<inter> negs x = {}"
    and "msgcs x (\<delta> x)"
using assms
proof (induct xs as poss negs msgcs arbitrary: \<delta> rule: abs_substs_set_induct)
  case (Cons y xs as poss negs msgcs)
  { case 1 thus ?case using Cons.hyps(1) unfolding abs_substs_fun_def by fastforce }

  { case 2 thus ?case
    proof (cases "x = y")
      case False
      then obtain \<delta>' where \<delta>':
          "\<delta>' \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs msgcs)" "\<delta>' x = \<delta> x"
        using 2 unfolding abs_substs_fun_def by force
      moreover have "x \<in> set xs" using 2(2) False by simp
      moreover have "\<exists>b. b \<in> set as \<and> poss y \<subseteq> b \<and> b \<inter> negs y = {}"
        using 2 False by auto
      ultimately show ?thesis using Cons.hyps(2) by fastforce
    qed (auto simp add: abs_substs_fun_def)
  }

  { case 3 thus ?case
    proof (cases "x = y")
      case False
      then obtain \<delta>' where \<delta>':
          "\<delta>' \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs msgcs)" "\<delta>' x = \<delta> x"
        using 3 unfolding abs_substs_fun_def by force
      moreover have "x \<in> set xs" using 3(2) False by simp
      moreover have "\<exists>b. b \<in> set as \<and> poss y \<subseteq> b \<and> b \<inter> negs y = {}"
        using 3 False by auto
      ultimately show ?thesis using Cons.hyps(3) by fastforce
    qed (auto simp add: abs_substs_fun_def)
  }

  { case 4 thus ?case
    proof (cases "x = y")
      case False
      then obtain \<delta>' where \<delta>':
          "\<delta>' \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs msgcs)" "\<delta>' x = \<delta> x"
        using 4 unfolding abs_substs_fun_def by force
      moreover have "x \<in> set xs" using 4(2) False by simp
      moreover have "\<exists>b. b \<in> set as \<and> poss y \<subseteq> b \<and> b \<inter> negs y = {}"
        using 4 False by auto
      ultimately show ?thesis using Cons.hyps(4) by fastforce
    qed (auto simp add: abs_substs_fun_def)
  }
qed (simp_all add: abs_substs_fun_def)

lemma abs_substs_abss_bounded':
  assumes "\<delta> \<in> abs_substs_fun ` set (abs_substs_set xs as poss negs msgcs)"
    and "x \<notin> set xs"
  shows "\<delta> x = {}"
using assms unfolding abs_substs_fun_def
by (induct xs as poss negs msgcs arbitrary: \<delta> rule: abs_substs_set_induct) (force, fastforce)

lemma transaction_poschecks_comp_unfold:
  "transaction_poschecks_comp C x = {s. \<exists>a. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> set C}"
proof (induction C)
  case (Cons c C) thus ?case
  proof (cases "\<exists>a y s. c = \<langle>a: Var y \<in> Fun (Set s) []\<rangle>")
    case True
    then obtain a y s where c: "c = \<langle>a: Var y \<in> Fun (Set s) []\<rangle>" by moura

    define f where "f \<equiv> transaction_poschecks_comp C"

    have "transaction_poschecks_comp (c#C) = f(y := insert s (f y))"
      using c by (simp add: f_def Let_def)
    moreover have "f x = {s. \<exists>a. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> set C}"
      using Cons.IH unfolding f_def by blast
    ultimately show ?thesis using c by auto
  next
    case False
    hence "transaction_poschecks_comp (c#C) = transaction_poschecks_comp C" (is ?P)
      using transaction_poschecks_comp.cases[of "c#C" ?P] by force
    thus ?thesis using False Cons.IH by auto
  qed
qed simp

lemma transaction_poschecks_comp_notin_fv_empty:
  assumes "x \<notin> fv\<^sub>s\<^sub>s\<^sub>t C"
  shows "transaction_poschecks_comp C x = {}"
using assms transaction_poschecks_comp_unfold[of C x] by fastforce

lemma transaction_negchecks_comp_unfold:
  "transaction_negchecks_comp C x = {s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> set C}"
proof (induction C)
  case (Cons c C) thus ?case
  proof (cases "\<exists>y s. c = \<langle>Var y not in Fun (Set s) []\<rangle>")
    case True
    then obtain y s where c: "c = \<langle>Var y not in Fun (Set s) []\<rangle>" by moura

    define f where "f \<equiv> transaction_negchecks_comp C"

    have "transaction_negchecks_comp (c#C) = f(y := insert s (f y))"
      using c by (simp add: f_def Let_def)
    moreover have "f x = {s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> set C}"
      using Cons.IH unfolding f_def by blast
    ultimately show ?thesis using c by auto
  next
    case False
    hence "transaction_negchecks_comp (c#C) = transaction_negchecks_comp C" (is ?P)
      using transaction_negchecks_comp.cases[of "c#C" ?P] 
      by force
    thus ?thesis using False Cons.IH by fastforce
  qed
qed simp  

lemma transaction_negchecks_comp_notin_fv_empty:
  assumes "x \<notin> fv\<^sub>s\<^sub>s\<^sub>t C"
  shows "transaction_negchecks_comp C x = {}"
using assms transaction_negchecks_comp_unfold[of C x] by fastforce

lemma transaction_check_preI[intro]:
  fixes T
  defines "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
    and "C \<equiv> set (unlabel (transaction_checks T))"
  assumes a0: "\<forall>x \<in> set (transaction_fresh T). \<delta> x = {}"
    and a1: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> \<delta> x \<in> set OCC"
    and a2: "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<delta>)"
    and a3: "\<forall>a x s. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<delta> x"
    and a4: "\<forall>x s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<notin> \<delta> x"
  shows "transaction_check_pre (FP, OCC, TI) T \<delta>"
proof -
  let ?P = "\<lambda>u. is_InSet u \<longrightarrow> (
    let x = the_elem_term u; s = the_set_term u
    in (is_Var x \<and> is_Fun_Set s) \<longrightarrow> the_Set (the_Fun s) \<in> \<delta> (the_Var x))"

  let ?Q = "\<lambda>u. (is_NegChecks u \<and> bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p u = [] \<and> the_eqs u = [] \<and> length (the_ins u) = 1) \<longrightarrow> (
    let x = fst (hd (the_ins u)); s = snd (hd (the_ins u))
    in (is_Var x \<and> is_Fun_Set s) \<longrightarrow> the_Set (the_Fun s) \<notin> \<delta> (the_Var x))"

  have 1: "?P u" when u: "u \<in> C" for u
    apply (unfold Let_def, intro impI, elim conjE)
    using u a3 Fun_Set_InSet_iff[of u] by metis

  have 2: "?Q u" when u: "u \<in> C" for u
    apply (unfold Let_def, intro impI, elim conjE)
    using u a4 Fun_Set_NotInSet_iff[of u] by metis

  show ?thesis
    using a0 a1 a2 1 2 fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
    unfolding transaction_check_pre_def \<theta>_def C_def Let_def
    by blast
qed

lemma transaction_check_pre_InSetE:
  assumes T: "transaction_check_pre FPT T \<delta>"
    and u: "u = \<langle>a: Var x \<in> Fun (Set s) []\<rangle>"
           "u \<in> set (unlabel (transaction_checks T))"
  shows "s \<in> \<delta> x"
proof -
  have "is_InSet u \<longrightarrow> is_Var (the_elem_term u) \<and> is_Fun_Set (the_set_term u) \<longrightarrow>
        the_Set (the_Fun (the_set_term u)) \<in> \<delta> (the_Var (the_elem_term u))"
    using T u unfolding transaction_check_pre_def Let_def by blast
  thus ?thesis using Fun_Set_InSet_iff[of u a x s] u by argo
qed

lemma transaction_check_pre_NotInSetE:
  assumes T: "transaction_check_pre FPT T \<delta>"
    and u: "u = \<langle>Var x not in Fun (Set s) []\<rangle>"
           "u \<in> set (unlabel (transaction_checks T))"
  shows "s \<notin> \<delta> x"
proof -
  have "is_NegChecks u \<and> bvars\<^sub>s\<^sub>s\<^sub>t\<^sub>p u = [] \<and> the_eqs u = [] \<and> length (the_ins u) = 1 \<longrightarrow>
         is_Var (fst (hd (the_ins u))) \<and> is_Fun_Set (snd (hd (the_ins u))) \<longrightarrow>
         the_Set (the_Fun (snd (hd (the_ins u)))) \<notin> \<delta> (the_Var (fst (hd (the_ins u))))"
    using T u unfolding transaction_check_pre_def Let_def by blast
  thus ?thesis using Fun_Set_NotInSet_iff[of u  x s] u by argo
qed

lemma transaction_check_pre_ReceiveE:
  defines "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
  assumes T: "transaction_check_pre (FP, OCC, TI) T \<delta>"
    and t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
  shows "intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<delta>)"
using T t unfolding transaction_check_pre_def Let_def \<theta>_def by blast

lemma transaction_check_compI[intro]:
  assumes T: "transaction_check_pre (FP, OCC, TI) T \<delta>"
    and T_adm: "admissible_transaction T"
    and x1: "\<forall>x. (x \<in> fv_transaction T - set (transaction_fresh T) \<and> fst x = TAtom Value)
                  \<longrightarrow> \<delta> x \<in> set OCC \<and> msgcs x (\<delta> x)"
    and x2: "\<forall>x. (x \<notin> fv_transaction T - set (transaction_fresh T) \<or> fst x \<noteq> TAtom Value)
                  \<longrightarrow> \<delta> x = {}"
  shows "\<delta> \<in> abs_substs_fun ` set (transaction_check_comp msgcs (FP, OCC, TI) T)"
proof -
  define S where "S \<equiv> unlabel (transaction_strand T)"
  define C where "C \<equiv> unlabel (transaction_checks T)"

  let ?xs = "fv_list\<^sub>s\<^sub>s\<^sub>t S"

  define poss where "poss \<equiv> transaction_poschecks_comp C"
  define negs where "negs \<equiv> transaction_negchecks_comp C"
  define ys where "ys \<equiv> filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) ?xs"

  have ys: "{x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value} = set ys"
    using fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of S]
    unfolding ys_def S_def by force
  
  have "\<delta> x \<in> set OCC" "msgcs x (\<delta> x)"
    when x: "x \<in> set ys" for x
    using x1 x ys by (blast, blast)
  moreover have "\<delta> x = {}"
    when x: "x \<notin> set ys" for x
    using x2 x ys by blast
  moreover have "poss x \<subseteq> \<delta> x" when x: "x \<in> set ys" for x
  proof -
    have "s \<in> \<delta> x" when u: "u = \<langle>a: Var x \<in> Fun (Set s) []\<rangle>" "u \<in> set C" for u a s
      using T u transaction_check_pre_InSetE[of "(FP, OCC, TI)" T \<delta>]
      unfolding C_def by blast
    thus ?thesis
      using transaction_poschecks_comp_unfold[of C x]
      unfolding poss_def by blast
  qed
  moreover have "\<delta> x \<inter> negs x = {}" when x: "x \<in> set ys" for x
  proof (cases "x \<in> fv\<^sub>s\<^sub>s\<^sub>t C")
    case True
    hence "s \<notin> \<delta> x" when u: "u = \<langle>Var x not in Fun (Set s) []\<rangle>" "u \<in> set C" for u s
      using T u transaction_check_pre_NotInSetE[of "(FP, OCC, TI)" T \<delta>]
      unfolding C_def by blast
    thus ?thesis
      using transaction_negchecks_comp_unfold[of C x]
      unfolding negs_def by blast
  next
    case False
    hence "negs x = {}"
      using x transaction_negchecks_comp_notin_fv_empty
      unfolding negs_def by blast
    thus ?thesis by blast
  qed
  ultimately have "\<delta> \<in> abs_substs_fun ` set (abs_substs_set ys OCC poss negs msgcs)"
    using abs_substs_has_abs[of ys \<delta> OCC poss negs msgcs]
    by fast
  thus ?thesis
    using T
    unfolding transaction_check_comp_def Let_def S_def C_def ys_def poss_def negs_def
    by fastforce
qed

context
begin
private lemma transaction_check_comp_in_aux:
  fixes T
  defines "C \<equiv> set (unlabel (transaction_checks T))"
  assumes T_adm: "admissible_transaction T"
    and a1: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          select\<langle>Var x, Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha> x)"
    and a2: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          \<langle>Var x in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha> x)"
    and a3: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          \<langle>Var x not in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<notin> \<alpha> x)"
  shows "\<forall>a x s. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha> x" (is ?A)
    and "\<forall>x s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<notin> \<alpha> x" (is ?B)
proof -
  note * = admissible_transaction_strand_step_cases(2,3)[OF T_adm]

  have 1: "fst x = TAtom Value" "x \<in> fv_transaction T - set (transaction_fresh T)"
    when x: "\<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> C" for a x s
    using * x unfolding C_def by fast+

  have 2: "fst x = TAtom Value" "x \<in> fv_transaction T - set (transaction_fresh T)"
    when x: "\<langle>Var x not in Fun (Set s) []\<rangle> \<in> C" for x s
    using * x unfolding C_def by fast+

  show ?A
  proof (intro allI impI)
    fix a x s assume u: "\<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> C"
    thus "s \<in> \<alpha> x" using 1 a1 a2 by (cases a) metis+
  qed

  show ?B
  proof (intro allI impI)
    fix x s assume u: "\<langle>Var x not in Fun (Set s) []\<rangle> \<in> C"
    thus "s \<notin> \<alpha> x" using 2 a3 by meson
  qed
qed

lemma transaction_check_comp_in:
  fixes T
  defines "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
    and "C \<equiv> set (unlabel (transaction_checks T))"
  assumes T_adm: "admissible_transaction T"
    and a1: "\<forall>x \<in> set (transaction_fresh T). \<alpha> x = {}"
    and a2: "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<alpha>)"
    and a3: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). \<forall>s.
          select\<langle>Var x, Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha> x"
    and a4: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). \<forall>s.
          \<langle>Var x in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha> x"
    and a5: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). \<forall>s.
          \<langle>Var x not in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<notin> \<alpha> x"
    and a6: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
          fst x = TAtom Value \<longrightarrow> \<alpha> x \<in> set OCC"
    and a7: "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
          fst x = TAtom Value \<longrightarrow> msgcs x (\<alpha> x)"
  shows "\<exists>\<delta> \<in> abs_substs_fun ` set (transaction_check_comp msgcs (FP, OCC, TI) T).
          \<forall>x \<in> fv_transaction T. fst x = TAtom Value \<longrightarrow> \<alpha> x = \<delta> x"
proof -
  let ?xs = "fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T))"
  let ?ys = "filter (\<lambda>x. x \<notin> set (transaction_fresh T)) ?xs"

  define \<alpha>' where "\<alpha>' \<equiv> \<lambda>x.
    if x \<in> fv_transaction T - set (transaction_fresh T) \<and> fst x = TAtom Value
    then \<alpha> x
    else {}"

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  have \<theta>\<alpha>_Fun: "is_Fun (t \<cdot> \<theta> \<alpha>) \<longleftrightarrow> is_Fun (t \<cdot> \<theta> \<alpha>')" for t
    unfolding \<alpha>'_def \<theta>_def
    by (induct t) auto

  have "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<alpha>')"
  proof (intro ballI impI)
    fix t assume t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"

    have 1: "intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<alpha>)"
      using t a2
      by auto

    obtain r where r:
        "r \<in> set (unlabel (transaction_receive T))"
        "t \<in> trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p r"
      using t by auto
    hence "\<exists>ts. r = receive\<langle>ts\<rangle> \<and> t \<in> set ts"
      using wellformed_transaction_unlabel_cases(1)[OF T_wf]
      by fastforce
    hence 2: "fv t \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)" using r by force

    have "fv t \<subseteq> fv_transaction T"
      by (metis (no_types, lifting) 2 transaction_strand_def sst_vars_append_subset(1)
                unlabel_append subset_Un_eq sup.bounded_iff)
    moreover have "fv t \<inter> set (transaction_fresh T) = {}"
      using 2 T_wf vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_receive T)"]
      unfolding wellformed_transaction_def
      by fast
    ultimately have "\<theta> \<alpha> x = \<theta> \<alpha>' x" when "x \<in> fv t" for x
      using that unfolding \<alpha>'_def \<theta>_def by fastforce
    hence 3: "t \<cdot> \<theta> \<alpha> = t \<cdot> \<theta> \<alpha>'"
      using term_subst_eq by blast

    show "intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<alpha>')" using 1 3 by simp
  qed
  moreover have
      "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          select\<langle>Var x, Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha>' x)"
      "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          \<langle>Var x in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha>' x)"
      "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value \<longrightarrow> (\<forall>s.
          \<langle>Var x not in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<notin> \<alpha>' x)"
    using a3 a4 a5
    unfolding \<alpha>'_def \<theta>_def C_def
    by meson+
  hence "\<forall>a x s. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<in> \<alpha>' x"
        "\<forall>x s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> C \<longrightarrow> s \<notin> \<alpha>' x"
    using transaction_check_comp_in_aux[OF T_adm, of \<alpha>']
    unfolding C_def
    by (fast, fast)
  ultimately have 4: "transaction_check_pre (FP, OCC, TI) T \<alpha>'"
    using a6 transaction_check_preI[of T \<alpha>' OCC FP TI]
    unfolding \<alpha>'_def \<theta>_def C_def
    by simp

  have 5: "\<forall>x \<in> fv_transaction T. fst x = TAtom Value \<longrightarrow> \<alpha> x = \<alpha>' x"
    using a1 by (auto simp add: \<alpha>'_def)

  have 6: "\<alpha>' \<in> abs_substs_fun ` set (transaction_check_comp msgcs (FP, OCC, TI) T)"
    using transaction_check_compI[OF 4 T_adm, of msgcs] a6 a7
    unfolding \<alpha>'_def 
    by auto

  show ?thesis using 5 6 by blast
qed
end

lemma transaction_check_trivial_case:
  assumes "transaction_updates T = []"
    and "transaction_send T = []"
  shows "transaction_check FPT T"
using assms
by (simp add: list_all_iff transaction_check_def transaction_check'_def transaction_check_post_def)

end


subsection \<open>Automatically Checking Protocol Security in a Typed Model\<close>
context stateful_protocol_model
begin

definition abs_intruder_knowledge ("\<alpha>\<^sub>i\<^sub>k") where
  "\<alpha>\<^sub>i\<^sub>k S \<I> \<equiv> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<I>)"

definition abs_value_constants ("\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s") where
  "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s S \<I> \<equiv> {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []} \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t S \<I>)"

definition abs_term_implications ("\<alpha>\<^sub>t\<^sub>i") where
  "\<alpha>\<^sub>t\<^sub>i \<A> T \<theta> \<I> \<equiv> {(s,t) | s t x.
    s \<noteq> t \<and> x \<in> fv_transaction T \<and> x \<notin> set (transaction_fresh T) \<and>
    Fun (Abs s) [] = \<theta> x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<and>
    Fun (Abs t) [] = \<theta> x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I>)}"

lemma abs_intruder_knowledge_append:
  "\<alpha>\<^sub>i\<^sub>k (A@B) \<I> =
    (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) \<I>) \<union>
    (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) \<I>)"
by (metis unlabel_append abs_set_union image_Un ik\<^sub>s\<^sub>s\<^sub>t_append abs_intruder_knowledge_def)

lemma abs_value_constants_append:
  fixes A B::"('a,'b,'c,'d) prot_strand"
  shows "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s (A@B) \<I> =
      {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []} \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) \<I>) \<union>
      {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []} \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@B) \<I>)"
proof -
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>s\<^sub>s\<^sub>t (unlabel (A@B)) \<I>)"
  define M where "M \<equiv> \<lambda>a::('a,'b,'c,'d) prot_strand.
                            {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t a) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []}"

  have "M (A@B) = M A \<union> M B"
    using unlabel_append[of A B] trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel A" "unlabel B"]
          image_Un[of "\<lambda>x. x \<cdot> \<I>" "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"]
    unfolding M_def by force
  hence "M (A@B) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0 = (M A \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0) \<union> (M B \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0)" by (simp add: abs_set_union)
  thus ?thesis unfolding abs_value_constants_def a0_def M_def by force 
qed

lemma transaction_renaming_subst_has_no_pubconsts_abss:
  fixes \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_renaming_subst \<alpha> P A"
  shows "subst_range \<alpha> \<inter> pubval_terms = {}" (is ?A)
    and "subst_range \<alpha> \<inter> abs_terms = {}" (is ?B)
proof -
  { fix t assume "t \<in> subst_range \<alpha>"
    then obtain x where "t = Var x" 
      using transaction_renaming_subst_is_renaming(1)[OF assms]
      by force
    hence "t \<notin> pubval_terms" "t \<notin> abs_terms" by simp_all
  } thus ?A ?B by auto
qed

lemma transaction_fresh_subst_has_no_pubconsts_abss:
  fixes \<sigma>::"('fun,'atom,'sets,'lbl) prot_subst"
  assumes "transaction_fresh_subst \<sigma> T \<A>" "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
  shows "subst_range \<sigma> \<inter> pubval_terms = {}" (is ?A)
    and "subst_range \<sigma> \<inter> abs_terms = {}" (is ?B)
proof -
  { fix t assume "t \<in> subst_range \<sigma>"
    then obtain x where "x \<in> set (transaction_fresh T)" "\<sigma> x = t"
      using assms(1) unfolding transaction_fresh_subst_def by auto
    then obtain n where "t = Fun (Val n) []" 
      using transaction_fresh_subst_sends_to_val[OF assms(1)] assms(2)
      by meson
    hence "t \<notin> pubval_terms" "t \<notin> abs_terms" unfolding is_PubConstValue_def by simp_all
  } thus ?A ?B by auto
qed

lemma reachable_constraints_GSMP_no_pubvals_abss:
  assumes "\<A> \<in> reachable_constraints P"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and \<I>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
           "\<forall>n. PubConst Value n \<notin> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
           "\<forall>n. Abs n \<notin> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
  shows "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (\<Union>T \<in> set P. trms_transaction T) - (pubval_terms \<union> abs_terms)"
    (is "?A \<subseteq> ?B")
using assms(1) \<I>(4,5)
proof (induction \<A> rule: reachable_constraints.induct)
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  define trms_P where "trms_P \<equiv> (\<Union>T \<in> set P. trms_transaction T)"
  define T' where "T' \<equiv> transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  have \<xi>_elim: "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = \<sigma> \<circ>\<^sub>s \<alpha>"
    using admissible_transaction_decl_subst_empty[OF bspec[OF P step.hyps(2)] step.hyps(3)]
    by simp

  note T_fresh = admissible_transactionE(2)[OF bspec[OF P step.hyps(2)]]
  note T_no_bvars = admissible_transactionE(4)[OF bspec[OF P step.hyps(2)]]

  have T_no_PubVal: "\<forall>T \<in> set P. \<forall>n. PubConst Value n \<notin> \<Union>(funs_term ` trms_transaction T)"
    and T_no_Abs: "\<forall>T \<in> set P. \<forall>n. Abs n \<notin> \<Union>(funs_term ` trms_transaction T)"
    using admissible_transactions_no_Value_consts''[OF bspec[OF P]] by metis+

  have \<I>': "\<forall>n. PubConst Value n \<notin> \<Union> (funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
           "\<forall>n. Abs n \<notin> \<Union> (funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
    using step.prems fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] unlabel_append[of \<A>]
    by auto

  have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))" for X
    using wt_subst_rm_vars[of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "set X"]
          transaction_decl_fresh_renaming_substs_wt[OF step.hyps(3-5)]
    by metis
  hence wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t ((rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<circ>\<^sub>s \<I>)" for X
    using \<I>(2) wt_subst_compose by fast

  have wftrms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range ((rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<circ>\<^sub>s \<I>))" for X
    using wf_trms_subst_compose[OF wf_trms_subst_rm_vars' \<I>(3)]
          transaction_decl_fresh_renaming_substs_range_wf_trms[OF step.hyps(3-5)]
    by fast

  have "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> ?B"
  proof
    fix t assume "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    hence "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq by blast
    then obtain s X where s:
        "s \<in> trms_transaction T"
        "t = s \<cdot> rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>"
        "set X \<subseteq> bvars_transaction T"
      using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_subst'' unfolding T'_def by blast

    define \<theta> where "\<theta> \<equiv> rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

    have 1: "s \<in> trms_P" using step.hyps(2) s(1) unfolding trms_P_def by auto

    have s_nin: "s \<notin> pubval_terms" "s \<notin> abs_terms"
      using 1 T_no_PubVal T_no_Abs funs_term_Fun_subterm
      unfolding trms_P_def is_PubConstValue_def is_Abs_def is_PubConst_def
      by (fastforce, blast)

    have 2: "(\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')) \<inter> pubval_terms = {}"
            "(\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')) \<inter> abs_terms = {}"
            "subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<inter> pubval_terms = {}"
            "subst_range (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<inter> abs_terms = {}"
            "subst_range \<theta> \<inter> pubval_terms = {}"
            "subst_range \<theta> \<inter> abs_terms = {}"
            "(\<theta> ` fv s) \<inter> pubval_terms = {}"
            "(\<theta> ` fv s) \<inter> abs_terms = {}"
      unfolding T'_def \<theta>_def
      using step.prems funs_term_Fun_subterm
      apply (fastforce simp add: is_PubConstValue_def is_PubConst_def,
             fastforce simp add: is_Abs_def)
      using pubval_terms_subst_range_comp[OF 
              transaction_fresh_subst_has_no_pubconsts_abss(1)[OF step.hyps(4) T_fresh]
              transaction_renaming_subst_has_no_pubconsts_abss(1)[OF step.hyps(5)]]
            abs_terms_subst_range_comp[OF 
              transaction_fresh_subst_has_no_pubconsts_abss(2)[OF step.hyps(4) T_fresh]
              transaction_renaming_subst_has_no_pubconsts_abss(2)[OF step.hyps(5)]]
      unfolding is_PubConstValue_def is_PubConst_def is_Abs_def \<xi>_elim
      by (force,force,force,force,force,force)
    
    have "(\<I> ` fv (s \<cdot> \<theta>)) \<inter> pubval_terms = {}"
         "(\<I> ` fv (s \<cdot> \<theta>)) \<inter> abs_terms = {}"
    proof -
      have "\<theta> = \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "bvars_transaction T = {}" "vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' = fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'"
        using s(3) T_no_bvars step.hyps(2) rm_vars_empty
              vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel T'"]
              bvars\<^sub>s\<^sub>s\<^sub>t_subst[of "unlabel (transaction_strand T)" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
              unlabel_subst[of "transaction_strand T" "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
        unfolding \<theta>_def T'_def by simp_all
      hence "fv (s \<cdot> \<theta>) \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'"
        using trms\<^sub>s\<^sub>s\<^sub>t_fv_subst_subset[OF s(1), of \<theta>] unlabel_subst[of "transaction_strand T" \<theta>]
        unfolding T'_def by auto
      moreover have "fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<subseteq> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"
        using fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>" "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')"]
              unlabel_append[of \<A> "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t T'"]
              fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of T']
        by simp_all
      hence "\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<inter> pubval_terms = {}" "\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<inter> abs_terms = {}"
        using 2(1,2) by blast+
      ultimately show "(\<I> ` fv (s \<cdot> \<theta>)) \<inter> pubval_terms = {}" "(\<I> ` fv (s \<cdot> \<theta>)) \<inter> abs_terms = {}"
        by blast+
    qed
    hence \<sigma>\<alpha>\<I>_disj: "((\<theta> \<circ>\<^sub>s \<I>) ` fv s) \<inter> pubval_terms = {}" 
                    "((\<theta> \<circ>\<^sub>s \<I>) ` fv s) \<inter> abs_terms = {}" 
      using pubval_terms_subst_range_comp'[of \<theta> "fv s" \<I>]
            abs_terms_subst_range_comp'[of \<theta> "fv s" \<I>]
            2(7,8)
      by (simp_all add: subst_apply_fv_unfold)
    
    have 3: "t \<notin> pubval_terms" "t \<notin> abs_terms"
      using s(2) s_nin \<sigma>\<alpha>\<I>_disj
            pubval_terms_subst[of s "rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>"]
            pubval_terms_subst_range_disj[of "rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>" s]
            abs_terms_subst[of s "rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>"]
            abs_terms_subst_range_disj[of "rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<circ>\<^sub>s \<I>" s]
      unfolding \<theta>_def
      by blast+

    have "t \<in> SMP trms_P" "fv t = {}"
      by (metis s(2) SMP.Substitution[OF SMP.MP[OF 1] wt wftrms, of X], 
          metis s(2) subst_subst_compose[of s "rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)" \<I>]
                     interpretation_grounds[OF \<I>(1), of "s \<cdot> rm_vars (set X) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"])
    hence 4: "t \<in> GSMP trms_P" unfolding GSMP_def by simp
    
    show "t \<in> ?B" using 3 4 by (auto simp add: trms_P_def)
  qed
  thus ?case
    using step.IH[OF \<I>'] trms\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] unlabel_append[of \<A>]
          image_Un[of "\<lambda>x. x \<cdot> \<I>" "trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"]
    by (simp add: T'_def)
qed simp

lemma \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_aux:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
           "t = Fun (Val n) [] \<or> t = Var x"
    and neq:
      "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<noteq>
       t \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>)"
  shows "\<exists>y \<in> fv_transaction T - set (transaction_fresh T).
          t \<cdot> \<I> = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<and> \<Gamma>\<^sub>v y = TAtom Value"
proof -
  let ?\<A>' = "\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  let ?\<B> = "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"
  let ?\<B>' = "?\<B> \<cdot>\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
  let ?\<B>'' = "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"

  have \<I>_interp: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
    by (metis \<I> welltyped_constraint_model_def constraint_model_def,
        metis \<I> welltyped_constraint_model_def,
        metis \<I> welltyped_constraint_model_def constraint_model_def)

  have T_adm: "admissible_transaction T"
    using T P(1) by blast

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]
  note T_adm_upds = admissible_transaction_is_wellformed_transaction(3)[OF T_adm]

  have T_fresh_vars_value_typed: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    using T P(1) protocol_transaction_vars_TAtom_typed(3)[of T] P(1) by simp

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T_adm \<xi>]

  note \<xi>\<sigma>\<alpha>_wt = transaction_decl_fresh_renaming_substs_wt[OF \<xi> \<sigma> \<alpha>]

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)
  hence t_wf: "wf\<^sub>t\<^sub>r\<^sub>m t" using t by auto

  have \<A>_no_val_bvars: "\<not>TAtom Value \<sqsubseteq> \<Gamma>\<^sub>v x"
    when "x \<in> bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" for x
    using P(1) reachable_constraints_no_bvars \<A>_reach
          vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"] that
          admissible_transactionE(4)
    by fast

  have x': "x \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" when "t = Var x"
    using that t by (simp add: var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t)

  have "\<exists>f \<in> funs_term (t \<cdot> \<I>). is_Val f"
    using abs_eq_if_no_Val neq by metis
  hence "\<exists>n T. Fun (Val n) T \<sqsubseteq> t \<cdot> \<I>"
    using funs_term_Fun_subterm
    unfolding is_Val_def by fast
  hence "TAtom Value \<sqsubseteq> \<Gamma> (Var x)" when "t = Var x"
    using wt_subst_trm''[OF \<I>_wt, of "Var x"] that
          subtermeq_imp_subtermtypeeq[of "t \<cdot> \<I>"] wf_trm_subst[OF \<I>_wf, of t] t_wf
    by fastforce
  hence x_val: "\<Gamma>\<^sub>v x = TAtom Value" when "t = Var x"
    using reachable_constraints_vars_TAtom_typed[OF \<A>_reach P x'] that
    by fastforce
  hence x_fv: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" when "t = Var x" using x'
    using reachable_constraints_Value_vars_are_fv[OF \<A>_reach P x'] that
    by blast
  then obtain m where m: "t \<cdot> \<I> = Fun (Val m) []"
    using constraint_model_Value_term_is_Val[
            OF \<A>_reach welltyped_constraint_model_prefix[OF \<I>] P, of x]
          t(2) x_val
    by force
  hence 0: "\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) m \<noteq> \<alpha>\<^sub>0 (db\<^sub>s\<^sub>s\<^sub>t (unlabel \<A>@?\<B>'') \<I>) m"
    using neq by (simp add: unlabel_def)

  have t_val: "\<Gamma> t = TAtom Value" using x_val t by force

  obtain u s where s: "t \<cdot> \<I> = u \<cdot> \<I>" "insert\<langle>u,s\<rangle> \<in> set ?\<B>' \<or> delete\<langle>u,s\<rangle> \<in> set ?\<B>'"
    using to_abs_neq_imp_db_update[OF 0] m
    by (metis (no_types, lifting) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst subst_lsst_unlabel)
  then obtain u' s' where s':
      "u = u' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" "s = s' \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      "insert\<langle>u',s'\<rangle> \<in> set ?\<B> \<or> delete\<langle>u',s'\<rangle> \<in> set ?\<B>"
    using stateful_strand_step_mem_substD(4,5)
    by blast
  hence s'': "insert\<langle>u',s'\<rangle> \<in> set (unlabel (transaction_strand T)) \<or>
              delete\<langle>u',s'\<rangle> \<in> set (unlabel (transaction_strand T))"
    using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_unlabel_steps_iff(4,5)[of u' s' "transaction_strand T"]
    by simp_all
  then obtain y where y: "y \<in> fv_transaction T" "u' = Var y"
    using transaction_inserts_are_Value_vars[OF T_wf T_adm_upds, of u' s']
          transaction_deletes_are_Value_vars[OF T_wf T_adm_upds, of u' s']
          stateful_strand_step_fv_subset_cases(4,5)[of u' s' "unlabel (transaction_strand T)"]
    by auto
  hence 1: "t \<cdot> \<I> = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>" using y s(1) s'(1) by (metis subst_apply_term.simps(1)) 

  have 2: "y \<notin> set (transaction_fresh T)" when "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<noteq> \<sigma> y"
    using transaction_fresh_subst_grounds_domain[OF \<sigma>, of y] subst_compose[of \<sigma> \<alpha> y] that \<xi>_empty
    by (auto simp add: subst_ground_ident)

  have 3: "y \<notin> set (transaction_fresh T)" when "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    using 2 that \<sigma> unfolding transaction_fresh_subst_def by fastforce

  have 4: "\<forall>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
            (\<exists>B. prefix B \<A> \<and> x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<and> \<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B))"
    by (metis welltyped_constraint_model_prefix[OF \<I>]
              constraint_model_Value_var_in_constr_prefix[OF \<A>_reach _ P])

  have 5: "\<Gamma>\<^sub>v y = TAtom Value"
    using 1 t_val
          wt_subst_trm''[OF \<xi>\<sigma>\<alpha>_wt, of "Var y"]
          wt_subst_trm''[OF \<I>_wt, of t]
          wt_subst_trm''[OF \<I>_wt, of "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y"]
    by (auto simp del: subst_subst_compose)

  have "y \<notin> set (transaction_fresh T)"
  proof (cases "t = Var x")
    case True (* \<I> x occurs in \<A> but not in subst_range \<sigma>, so y cannot be fresh *)
    hence *: "\<I> x = Fun (Val m) []" "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" "\<I> x = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>"
      using m t(1) 1 x_fv x' by (force, blast, force)

    obtain B where B: "prefix B \<A>" "\<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      using *(2) 4 x_val[OF True] by fastforce
    hence "\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      using transaction_fresh_subst_range_fresh(1)[OF \<sigma>] trms\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset(1)[of B]
      unfolding prefix_def by fast
    thus ?thesis using *(1,3) B(2) 2 by (metis subst_imgI term.distinct(1))
  next
    case False
    hence "t \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" using t by simp
    thus ?thesis using 1 3 by argo
  qed
  thus ?thesis using 1 5 y(1) by fast
qed

lemma \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Var:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
  shows "\<I> x \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>) \<in>
            timpl_closure_set {\<I> x \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)} (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>)"
proof -
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>)"
  define a3 where "a3 \<equiv> \<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>"

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)

  have T_adm: "admissible_transaction T" by (metis P(1) T)

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T_adm \<xi>]

  note \<xi>\<sigma>\<alpha>_wt = transaction_decl_fresh_renaming_substs_wt[OF \<xi> \<sigma> \<alpha>]

  have \<I>_interp: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
    by (metis \<I> welltyped_constraint_model_def constraint_model_def,
        metis \<I> welltyped_constraint_model_def,
        metis \<I> welltyped_constraint_model_def constraint_model_def)

  have "\<Gamma>\<^sub>v x = Var Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = Var (prot_atom.Atom a))"
    using reachable_constraints_vars_TAtom_typed[OF \<A>_reach P, of x]
          x vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"]
    by auto

  hence "\<I> x \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {\<I> x \<cdot>\<^sub>\<alpha> a0} a3"
  proof
    assume x_val: "\<Gamma>\<^sub>v x = TAtom Value"
    show "\<I> x \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {\<I> x \<cdot>\<^sub>\<alpha> a0} a3"
    proof (cases "\<I> x \<cdot>\<^sub>\<alpha> a0 = \<I> x \<cdot>\<^sub>\<alpha> a0'")
      case False
      hence "\<exists>y \<in> fv_transaction T - set (transaction_fresh T).
              \<I> x = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<and> \<Gamma>\<^sub>v y = TAtom Value"
        using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_aux[OF \<A>_reach T \<I> \<xi> \<sigma> \<alpha> P fv\<^sub>s\<^sub>s\<^sub>t_is_subterm_trms\<^sub>s\<^sub>s\<^sub>t[OF x], of _ x]
        unfolding a0_def a0'_def
        by fastforce
      then obtain y where y:
          "y \<in> fv_transaction T - set (transaction_fresh T)"
          "\<I> x = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>"
          "\<I> x \<cdot>\<^sub>\<alpha> a0 = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0"
          "\<I> x \<cdot>\<^sub>\<alpha> a0' = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'"
          "\<Gamma>\<^sub>v y = TAtom Value"
        by metis
      then obtain n where n: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val n) []"
        using \<Gamma>\<^sub>v_TAtom''(2)[of y] x x_val
              transaction_var_becomes_Val[
                OF reachable_constraints.step[OF \<A>_reach T \<xi> \<sigma> \<alpha>] \<I> \<xi> \<sigma> \<alpha> P T, of y]
        by force

      have "a0 n \<noteq> a0' n"
           "y \<in> fv_transaction T"
           "y \<notin> set (transaction_fresh T)"
           "absc (a0 n) = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0"
           "absc (a0' n) = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'"
        using y n False by force+
      hence 1: "(a0 n, a0' n) \<in> a3" 
        unfolding a0_def a0'_def a3_def abs_term_implications_def
        by blast
      
      have 2: "\<I> x \<cdot>\<^sub>\<alpha> a0' \<in> set \<langle>a0 n --\<guillemotright> a0' n\<rangle>\<langle>\<I> x \<cdot>\<^sub>\<alpha> a0\<rangle>"
        using y n timpl_apply_const by auto

      show ?thesis
        using timpl_closure.TI[OF timpl_closure.FP 1] 2
              term_variants_pred_iff_in_term_variants[
                of "(\<lambda>_. [])(Abs (a0 n) := [Abs (a0' n)])"]
        unfolding timpl_closure_set_def timpl_apply_term_def
        by auto
    qed (auto intro: timpl_closure_setI)
  next
    assume "\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a)"
    then obtain a where x_atom: "\<Gamma>\<^sub>v x = TAtom (Atom a)" by moura

    obtain f T where fT: "\<I> x = Fun f T"
      using interpretation_grounds[OF \<I>_interp, of "Var x"]
      by (cases "\<I> x") auto

    have fT_atom: "\<Gamma> (Fun f T) = TAtom (Atom a)"
      using wt_subst_trm''[OF \<I>_wt, of "Var x"] x_atom fT
      by simp

    have T: "T = []"
      using fT wf_trm_subst[OF \<I>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s, of "Var x"] const_type_inv_wf[OF fT_atom]
      by fastforce

    have f: "\<not>is_Val f" using fT_atom unfolding is_Val_def by auto

    have "\<I> x \<cdot>\<^sub>\<alpha> b = \<I> x" for b
      using T fT abs_term_apply_const(2)[OF f]
      by auto
    thus "\<I> x \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {\<I> x \<cdot>\<^sub>\<alpha> a0} a3"
      by (auto intro: timpl_closure_setI)
  qed
  thus ?thesis by (metis a0_def a0'_def a3_def)
qed

lemma \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Val:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and n: "Fun (Val n) [] \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  shows "Fun (Val n) [] \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>) \<in>
            timpl_closure_set {Fun (Val n) [] \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)} (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>)"
proof -
  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') \<I>)"
  define a3 where "a3 \<equiv> \<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>"

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)

  have T_adm: "admissible_transaction T" by (metis P(1) T)

  have "Fun (Abs (a0' n)) [] \<in> timpl_closure_set {Fun (Abs (a0 n)) []} a3"
  proof (cases "a0 n = a0' n")
    case False
    then obtain x where x:
        "x \<in> fv_transaction T - set (transaction_fresh T)" "Fun (Val n) [] = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I>"
      using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_aux[OF \<A>_reach T \<I> \<xi> \<sigma> \<alpha> P n]
      by (fastforce simp add: a0_def a0'_def T'_def)
    hence "absc (a0 n) = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0" "absc (a0' n) = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'" by simp_all
    hence 1: "(a0 n, a0' n) \<in> a3"
      using False x(1)
      unfolding a0_def a0'_def a3_def abs_term_implications_def T'_def
      by blast
    show ?thesis
      using timpl_apply_Abs[of "[]" "[]" "a0 n" "a0' n"]
            timpl_closure.TI[OF timpl_closure.FP[of "Fun (Abs (a0 n)) []" a3] 1]
            term_variants_pred_iff_in_term_variants[of "(\<lambda>_. [])(Abs (a0 n) := [Abs (a0' n)])"]
      unfolding timpl_closure_set_def timpl_apply_term_def
      by force
  qed (auto intro: timpl_closure_setI)
  thus ?thesis by (simp add: a0_def a0'_def a3_def T'_def)
qed

lemma \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_ik:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and t: "t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
  shows "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>) \<in>
            timpl_closure_set {t \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)} (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>)"
proof -
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>)"
  define a3 where "a3 \<equiv> \<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>"

  let ?U = "\<lambda>T a. map (\<lambda>s. s \<cdot> \<I> \<cdot>\<^sub>\<alpha> a) T"

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)

  have T_adm: "admissible_transaction T" by (metis P(1) T)

  have "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" "wf\<^sub>t\<^sub>r\<^sub>m t" using \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s t ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset by force+
  hence "\<forall>t0 \<in> subterms t. t0 \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {t0 \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0} a3"
  proof (induction t)
    case (Var x) thus ?case
      using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Var[OF \<A>_reach T \<I> \<xi> \<sigma> \<alpha> P, of x]
            ik\<^sub>s\<^sub>s\<^sub>t_var_is_fv[of x "unlabel \<A>"] vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"]
      by (simp add: a0_def a0'_def a3_def)
  next
    case (Fun f S)
    have IH: "\<forall>t0 \<in> subterms t. t0 \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {t0 \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0} a3"
      when "t \<in> set S" for t
      using that Fun.prems(1) wf_trm_param[OF Fun.prems(2)] Fun.IH
      by (meson in_subterms_subset_Union params_subterms subsetCE)
    hence "t \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {t \<cdot>\<^sub>\<alpha> a0} a3"
      when "t \<in> set (map (\<lambda>s. s \<cdot> \<I>) S)" for t
      using that by auto
    hence "t \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure (t \<cdot>\<^sub>\<alpha> a0) a3"
      when "t \<in> set (map (\<lambda>s. s \<cdot> \<I>) S)" for t
      using that timpl_closureton_is_timpl_closure by auto
    hence "(t \<cdot>\<^sub>\<alpha> a0, t \<cdot>\<^sub>\<alpha> a0') \<in> timpl_closure' a3"
      when "t \<in> set (map (\<lambda>s. s \<cdot> \<I>) S)" for t
      using that timpl_closure_is_timpl_closure' by auto
    hence IH': "((?U S a0) ! i, (?U S a0') ! i) \<in> timpl_closure' a3"
      when "i < length (map (\<lambda>s. s \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0) S)" for i
      using that by auto

    show ?case
    proof (cases "\<exists>n. f = Val n")
      case True
      then obtain n where "Fun f S = Fun (Val n) []"
        using Fun.prems(2) unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by force
      moreover have "Fun f S \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
        using ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset Fun.prems(1) by blast
      ultimately show ?thesis
        using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Val[OF \<A>_reach T \<I> \<xi> \<sigma> \<alpha> P]
        by (simp add: a0_def a0'_def a3_def)
    next
      case False
      hence "Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a = Fun f (map (\<lambda>t. t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a) S)" for a by (cases f) simp_all
      hence "(Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0, Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0') \<in> timpl_closure' a3"
        using timpl_closure_FunI[OF IH']
        by simp
      hence "Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {Fun f S \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0} a3"
        using timpl_closureton_is_timpl_closure
              timpl_closure_is_timpl_closure'
        by metis
      thus ?thesis using IH by simp
    qed
  qed
  thus ?thesis by (simp add: a0_def a0'_def a3_def)
qed

lemma transaction_prop1:
  assumes "\<delta> \<in> abs_substs_fun ` set (transaction_check_comp msgcs (FP, OCC, TI) T)"
    and "x \<in> fv_transaction T"
    and "x \<notin> set (transaction_fresh T)"
    and "\<delta> x \<noteq> absdbupd (unlabel (transaction_updates T)) x (\<delta> x)"
    and "transaction_check' msgcs (FP, OCC, TI) T"
    and TI: "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
  shows "(\<delta> x, absdbupd (unlabel (transaction_updates T)) x (\<delta> x)) \<in> (set TI)\<^sup>+"
proof -
  let ?upd = "\<lambda>x. absdbupd (unlabel (transaction_updates T)) x (\<delta> x)"

  have 0: "fv_transaction T = set (fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T)))"
    by (metis fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]) 

  have 1: "transaction_check_post (FP, OCC, TI) T \<delta>"
    using assms(1,5)
    unfolding transaction_check_def transaction_check'_def list_all_iff
    by blast

  have "(\<delta> x, ?upd x) \<in> set TI \<longleftrightarrow> (\<delta> x, ?upd x) \<in> (set TI)\<^sup>+"
    using TI using assms(4) by blast
  thus ?thesis
    using assms(2,3,4) 0 1 in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
    unfolding transaction_check_post_def List.member_def Let_def by blast
qed

lemma transaction_prop2:
  assumes \<delta>: "\<delta> \<in> abs_substs_fun ` set (transaction_check_comp msgcs (FP, OCC, TI) T)"
    and x: "x \<in> fv_transaction T" "fst x = TAtom Value"
    and T_check: "transaction_check' msgcs (FP, OCC, TI) T"
    and T_adm: "admissible_transaction T"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
  shows "x \<notin> set (transaction_fresh T) \<Longrightarrow> \<delta> x \<in> set OCC" (is "?A' \<Longrightarrow> ?A")
    and "absdbupd (unlabel (transaction_updates T)) x (\<delta> x) \<in> set OCC" (is ?B)
proof -
  let ?xs = "fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T))"
  let ?ys = "filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) ?xs"
  let ?C = "unlabel (transaction_checks T)"
  let ?poss = "transaction_poschecks_comp ?C"
  let ?negs = "transaction_negchecks_comp ?C"
  let ?\<delta>upd = "\<lambda>y. absdbupd (unlabel (transaction_updates T)) y (\<delta> y)"

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]
  note T_occ = admissible_transaction_is_wellformed_transaction(5)[OF T_adm]

  have 0: "{x \<in> fv_transaction T - set (transaction_fresh T). fst x = TAtom Value} = set ?ys"
    using fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
    by force

  have 1: "transaction_check_pre (FP, OCC, TI) T \<delta>"
    using \<delta> unfolding transaction_check_comp_def Let_def by fastforce

  have 2: "transaction_check_post (FP, OCC, TI) T \<delta>"
    using \<delta> T_check unfolding transaction_check_def transaction_check'_def list_all_iff by auto

  have 3: "\<delta> \<in> abs_substs_fun ` set (abs_substs_set ?ys OCC ?poss ?negs msgcs)"
    using \<delta> unfolding transaction_check_comp_def Let_def by force

  show A: ?A when ?A' using that 0 3 x abs_substs_abss_bounded by blast

  have 4: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_updates T) \<union> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
    when x': "x \<in> set (transaction_fresh T)"
    using x' admissible_transactionE(7)[OF T_adm] by blast

  have "intruder_synth_mod_timpls FP TI (occurs (absc (?\<delta>upd x)))"
    when x': "x \<in> set (transaction_fresh T)"
  proof -
    obtain l ts S where ts:
        "transaction_send T = (l,send\<langle>ts\<rangle>)#S" "occurs (Var x) \<in> set ts"
      using admissible_transaction_occurs_checksE2[OF T_occ x'] by blast
    hence "occurs (Var x) \<in> set ts" "send\<langle>ts\<rangle> \<in> set (unlabel (transaction_send T))"
      using x' unfolding suffix_def by (fastforce, fastforce)
    thus ?thesis using 2 x unfolding transaction_check_post_def by fastforce
  qed
  hence "timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c occurs (absc (?\<delta>upd x))"
    when x': "x \<in> set (transaction_fresh T)"
    using x' intruder_synth_mod_timpls_is_synth_timpl_closure_set[
            OF TI, of FP "occurs (absc (?\<delta>upd x))"]
    by argo
  hence "Abs (?\<delta>upd x) \<in> \<Union>(funs_term ` timpl_closure_set (set FP) (set TI))"
    when x': "x \<in> set (transaction_fresh T)"
    using x' ideduct_synth_priv_fun_in_ik[
            of "timpl_closure_set (set FP) (set TI)" "occurs (absc (?\<delta>upd x))"]
    by simp
  hence "\<exists>t \<in> timpl_closure_set (set FP) (set TI). Abs (?\<delta>upd x) \<in> funs_term t"
    when x': "x \<in> set (transaction_fresh T)"
    using x' by force
  hence 5: "?\<delta>upd x \<in> set OCC" when x': "x \<in> set (transaction_fresh T)"
    using x' OCC by fastforce

  have 6: "?\<delta>upd x \<in> set OCC" when x': "x \<notin> set (transaction_fresh T)"
  proof (cases "\<delta> x = ?\<delta>upd x")
    case False
    hence "(\<delta> x, ?\<delta>upd x) \<in> (set TI)\<^sup>+" "\<delta> x \<in> set OCC"
      using A 2 x' x TI
      unfolding transaction_check_post_def fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t Let_def
                in_trancl_closure_iff_in_trancl_fun[symmetric]
                List.member_def
      by blast+
    thus ?thesis using timpl_closure_set_absc_subset_in[OF OCC(2)] by blast
  qed (simp add: A x' x(1))

  show ?B by (metis 5 6)
qed

lemma transaction_prop3:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
  shows "\<forall>x \<in> set (transaction_fresh T). (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc {}" (is ?A)
    and "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T).
            intruder_synth_mod_timpls FP TI (t \<cdot> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>))" (is ?B)
    and "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
         \<forall>s. select\<langle>Var x,Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))
                 \<longrightarrow> (\<exists>ss. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<in> ss)" (is ?C)
    and "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
         \<forall>s. \<langle>Var x in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))
                 \<longrightarrow> (\<exists>ss. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<in> ss)" (is ?D)
    and "\<forall>x \<in> fv_transaction T - set (transaction_fresh T).
         \<forall>s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))
                 \<longrightarrow> (\<exists>ss. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<notin> ss)" (is ?E)
    and "\<forall>x \<in> fv_transaction T - set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
         (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<in> absc ` set OCC" (is ?F)
proof -
  let ?T' = "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  let ?\<theta> = "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@?T') \<I>)"
  define fv_AT' where "fv_AT' \<equiv> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@?T')"

  have T_adm: "admissible_transaction T"
    using T P(1) by blast

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]
  note T_adm' = admissible_transaction_is_wellformed_transaction(2-4)[OF T_adm]

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T_adm \<xi>]
  hence \<xi>_elim: "?\<theta> = \<sigma> \<circ>\<^sub>s \<alpha>" by simp

  have \<I>': "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
           "\<forall>n. PubConst Value n \<notin> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
           "\<forall>n. Abs n \<notin> \<Union>(funs_term ` (\<I> ` fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
           "\<forall>n. PubConst Value n \<notin> \<Union>(funs_term ` (\<I> ` fv_AT'))"
           "\<forall>n. Abs n \<notin> \<Union>(funs_term ` (\<I> ` fv_AT'))"
    using \<I> admissible_transaction_occurs_checks_prop'[
            OF \<A>_reach welltyped_constraint_model_prefix[OF \<I>] P]
          admissible_transaction_occurs_checks_prop'[
            OF reachable_constraints.step[OF \<A>_reach T \<xi> \<sigma> \<alpha>] \<I> P]
    unfolding welltyped_constraint_model_def constraint_model_def is_Val_def is_Abs_def fv_AT'_def
    by (meson,meson,meson,metis,metis,metis,metis)

  have T_no_pubconsts: "\<forall>n. PubConst Value n \<notin> \<Union>(funs_term ` trms_transaction T)"
    and T_no_abss: "\<forall>n. Abs n \<notin> \<Union>(funs_term ` trms_transaction T)"
    and T_fresh_vars_value_typed: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    and T_fv_const_typed: "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    using protocol_transaction_vars_TAtom_typed
          protocol_transactions_no_pubconsts
          protocol_transactions_no_abss
          funs_term_Fun_subterm P T
    by (fast, fast, fast, fast)

  have wt_\<sigma>\<alpha>\<I>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>)"
    using \<I>'(2) wt_subst_compose transaction_fresh_subst_wt[OF \<sigma>]
          transaction_renaming_subst_wt[OF \<alpha>]
    by blast

  have 1: "?\<theta> y \<cdot> \<I> = \<sigma> y" when "y \<in> set (transaction_fresh T)" for y
    using transaction_fresh_subst_grounds_domain[OF \<sigma> that] subst_compose[of \<sigma> \<alpha> y]
    unfolding \<xi>_elim by (simp add: subst_ground_ident)

  have 2: "?\<theta> y \<cdot> \<I> \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" when "y \<in> set (transaction_fresh T)" for y
    using 1[OF that] that \<sigma> unfolding transaction_fresh_subst_def by auto

  have 3: "\<forall>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
            (\<exists>B. prefix B \<A> \<and> x \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<and> \<I> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B))"
    by (metis welltyped_constraint_model_prefix[OF \<I>]
              constraint_model_Value_var_in_constr_prefix[OF \<A>_reach _ P])

  have 4: "\<exists>n. ?\<theta> y \<cdot> \<I> = Fun (Val n) []"
    when "y \<in> fv_transaction T" "\<Gamma>\<^sub>v y = TAtom Value" for y
    using transaction_var_becomes_Val[OF reachable_constraints.step[OF \<A>_reach T \<xi> \<sigma> \<alpha>] \<I> \<xi> \<sigma> \<alpha> P T]
          that T_fv_const_typed \<Gamma>\<^sub>v_TAtom''[of y]
    by metis

  have \<I>_is_T_model: "strand_sem_stateful (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) (set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)) (unlabel ?T') \<I>"
    using \<I> unlabel_append[of \<A> ?T'] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>" \<I> "[]"]
          strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" "unlabel ?T'" \<I>]
    by (simp add: welltyped_constraint_model_def constraint_model_def db\<^sub>s\<^sub>s\<^sub>t_def)

  have T_rcv_no_val_bvars: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<inter> subst_domain ?\<theta> = {}"
    using admissible_transaction_no_bvars[OF T_adm] bvars_transaction_unfold[of T] by blast

  show ?A
  proof
    fix y assume y: "y \<in> set (transaction_fresh T)"
    then obtain yn where yn: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val yn) []" "Fun (Val yn) [] \<in> subst_range \<sigma>"
      by (metis \<xi>_elim T_fresh_vars_value_typed transaction_fresh_subst_sends_to_val'[OF \<sigma>])

    { \<comment> \<open>since \<open>y\<close> is fresh \<open>(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>\<close> cannot be part of the database state of \<open>\<I> \<A>\<close>\<close>
      fix t' s assume t': "insert\<langle>t',s\<rangle> \<in> set (unlabel \<A>)" "t' \<cdot> \<I> = Fun (Val yn) []"
      then obtain z where t'_z: "t' = Var z" using 2[OF y] yn(1) by (cases t') auto
      hence z: "z \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" "\<I> z = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>" using t' yn(1) by force+
      hence z': "\<Gamma>\<^sub>v z = TAtom Value"
        by (metis \<Gamma>.simps(1) \<Gamma>_consts_simps(2) t'(2) t'_z wt_subst_trm'' \<I>'(2))

      obtain B where B: "prefix B \<A>" "\<I> z \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)" using z z' 3 by fastforce
      hence "\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
        using transaction_fresh_subst_range_fresh(1)[OF \<sigma>] trms\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset(1)[of B]
        unfolding prefix_def by fast
      hence False using B(2) 1[OF y] z yn(1) by (metis subst_imgI term.distinct(1)) 
    } hence "\<nexists>s. (?\<theta> y \<cdot> \<I>, s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using db\<^sub>s\<^sub>s\<^sub>t_in_cases[of "?\<theta> y \<cdot> \<I>" _ "unlabel \<A>" \<I> "[]"] yn(1)
      by (force simp add: db\<^sub>s\<^sub>s\<^sub>t_def)
    thus "?\<theta> y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc {}"
      using to_abs_empty_iff_notin_db[of yn "db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I> []"] yn(1)
      by (simp add: db\<^sub>s\<^sub>s\<^sub>t_def)
  qed

  show receives_covered: ?B
  proof
    fix t assume t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
    hence t_in_T: "t \<in> trms_transaction T"
      using trms\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset(1)[of "transaction_receive T"]
      unfolding transaction_strand_def by fast

    obtain ts where ts: "t \<in> set ts" "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T))"
      using t wellformed_transaction_send_receive_trm_cases(1)[OF T_wf] by blast

    have t_rcv: "receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t ?\<theta>\<rangle> \<in> set (unlabel (transaction_receive T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?\<theta>))"
      using subst_lsst_unlabel_member[of "receive\<langle>ts\<rangle>" "transaction_receive T" ?\<theta>]
            trms\<^sub>s\<^sub>s\<^sub>t_in[OF t] ts
      by fastforce
    
    have "list_all (\<lambda>t. ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> ?\<theta> \<cdot> \<I>) ts"
      using wellformed_transaction_sem_receives[OF T_wf \<I>_is_T_model t_rcv]
      unfolding list_all_iff by fastforce
    hence *: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> ?\<theta> \<cdot> \<I>" using ts(1) unfolding list_all_iff by fast

    have t_fv: "fv (t \<cdot> ?\<theta>) \<subseteq> fv_AT'"
      using fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] unlabel_append[of \<A>]
            fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?\<theta>"]
            ts(1) t_rcv fv_transaction_subst_unfold[of T ?\<theta>]
      unfolding fv_AT'_def by force

    have **: "\<forall>t \<in> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
      using FP(3) by (auto simp add: a0_def abs_intruder_knowledge_def)

    note lms1 = pubval_terms_subst[OF _ pubval_terms_subst_range_disj[
                  OF transaction_fresh_subst_has_no_pubconsts_abss(1)[OF \<sigma>], of t]]
                pubval_terms_subst[OF _ pubval_terms_subst_range_disj[
                  OF transaction_renaming_subst_has_no_pubconsts_abss(1)[OF \<alpha>], of "t \<cdot> \<sigma>"]]

    note lms2 = abs_terms_subst[OF _ abs_terms_subst_range_disj[
                  OF transaction_fresh_subst_has_no_pubconsts_abss(2)[OF \<sigma>], of t]]
                abs_terms_subst[OF _ abs_terms_subst_range_disj[
                  OF transaction_renaming_subst_has_no_pubconsts_abss(2)[OF \<alpha>], of "t \<cdot> \<sigma>"]]

    have "t \<in> (\<Union>T\<in>set P. trms_transaction T)" "fv (t \<cdot> \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I>) = {}"
      using t_in_T T interpretation_grounds[OF \<I>'(1)] by fast+
    moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>))"
      using wf_trm_subst_rangeI[of \<sigma>, OF transaction_fresh_subst_is_wf_trm[OF \<sigma>]]
            wf_trm_subst_rangeI[of \<alpha>, OF transaction_renaming_subst_is_wf_trm[OF \<alpha>]]
            wf_trms_subst_compose[of \<sigma> \<alpha>, THEN wf_trms_subst_compose[OF _ \<I>'(3)]]
      by blast
    moreover
    have "t \<notin> pubval_terms"
      using t_in_T T_no_pubconsts funs_term_Fun_subterm
      unfolding is_PubConstValue_def is_PubConst_def by fastforce
    hence "t \<cdot> ?\<theta> \<notin> pubval_terms"
      using lms1 T_fresh_vars_value_typed
      unfolding \<xi>_elim by auto
    hence "t \<cdot> ?\<theta> \<cdot> \<I> \<notin> pubval_terms"
      using \<I>'(6) t_fv pubval_terms_subst'[of "t \<cdot> ?\<theta>" \<I>]
      by auto
    moreover have "t \<notin> abs_terms"
      using t_in_T T_no_abss funs_term_Fun_subterm
      unfolding is_Abs_def by force
    hence "t \<cdot> ?\<theta> \<notin> abs_terms"
      using lms2 T_fresh_vars_value_typed
      unfolding \<xi>_elim by auto
    hence "t \<cdot> ?\<theta> \<cdot> \<I> \<notin> abs_terms"
      using \<I>'(7) t_fv abs_terms_subst'[of "t \<cdot> ?\<theta>" \<I>]
      by auto
    ultimately have ***:
        "t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<in> GSMP (\<Union>T\<in>set P. trms_transaction T) - (pubval_terms \<union> abs_terms)"
      using SMP.Substitution[OF SMP.MP[of t "\<Union>T\<in>set P. trms_transaction T"], of "\<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>"]
            subst_subst_compose[of t ?\<theta> \<I>] wt_\<sigma>\<alpha>\<I>
      unfolding GSMP_def \<xi>_elim by fastforce

    have ****:
        "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<subseteq> GSMP (\<Union>T\<in>set P. trms_transaction T) - (pubval_terms \<union> abs_terms)"
      using reachable_constraints_GSMP_no_pubvals_abss[OF \<A>_reach P \<I>'(1-5)]
            ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset[of "unlabel \<A>"]
      by blast

    show "intruder_synth_mod_timpls FP TI (t \<cdot> ?\<theta> \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>))"
      using deduct_FP_if_deduct[OF **** ** * ***] deducts_eq_if_analyzed[OF FP(1)]
            intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI, of FP]
      unfolding a0_def by force
  qed

  show ?C
  proof (intro ballI allI impI)
    fix y s
    assume y: "y \<in> fv_transaction T - set (transaction_fresh T)"
       and s: "select\<langle>Var y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))"
    hence "select\<langle>Var y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_strand T))"
      unfolding transaction_strand_def unlabel_def by auto
    hence y_val: "\<Gamma>\<^sub>v y = TAtom Value"
      using transaction_selects_are_Value_vars[OF T_wf T_adm'(1)]
      by fastforce

    have "select\<langle>?\<theta> y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?\<theta>))"
      using subst_lsst_unlabel_member[OF s]
      by fastforce
    hence "((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>, Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using wellformed_transaction_sem_pos_checks[
              OF T_wf \<I>_is_T_model,
              of Assign "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y" "Fun (Set s) []"]
      by simp
    thus "\<exists>ss. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<in> ss"
      using to_abs_alt_def[of "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>"] 4[of y] y y_val by auto
  qed

  show ?D
  proof (intro ballI allI impI)
    fix y s
    assume y: "y \<in> fv_transaction T - set (transaction_fresh T)"
       and s: "\<langle>Var y in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))"
    hence "\<langle>Var y in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_strand T))"
      unfolding transaction_strand_def unlabel_def by auto
    hence y_val: "\<Gamma>\<^sub>v y = TAtom Value"
      using transaction_inset_checks_are_Value_vars[OF T_adm]
      by fastforce

    have "\<langle>?\<theta> y in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?\<theta>))"
      using subst_lsst_unlabel_member[OF s]
      by fastforce
    hence "(?\<theta> y \<cdot> \<I>, Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using wellformed_transaction_sem_pos_checks[
              OF T_wf \<I>_is_T_model,
              of Check "?\<theta> y" "Fun (Set s) []"]
      by simp
    thus "\<exists>ss. ?\<theta> y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<in> ss"
      using to_abs_alt_def[of "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>"] 4[of y] y y_val by auto
  qed

  show ?E
  proof (intro ballI allI impI)
    fix y s
    assume y: "y \<in> fv_transaction T - set (transaction_fresh T)"
       and s: "\<langle>Var y not in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))"
    hence "\<langle>Var y not in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_strand T))"
      unfolding transaction_strand_def unlabel_def by auto
    hence y_val: "\<Gamma>\<^sub>v y = TAtom Value"
      using transaction_notinset_checks_are_Value_vars[OF T_adm]
      by fastforce

    have "\<langle>?\<theta> y not in Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?\<theta>))"
      using subst_lsst_unlabel_member[OF s]
      by fastforce
    hence "(?\<theta> y \<cdot> \<I>, Fun (Set s) []) \<notin> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using wellformed_transaction_sem_neg_checks(2)[
              OF T_wf \<I>_is_T_model,
              of "[]" "?\<theta> y" "Fun (Set s) []"]
      by simp
    moreover have "list_all admissible_transaction_updates P"
      using Ball_set[of P "admissible_transaction"] P(1)
            Ball_set[of P admissible_transaction_updates]
            admissible_transaction_is_wellformed_transaction(3)
      by fast
    moreover have "list_all wellformed_transaction P"
      using P(1) Ball_set[of P "admissible_transaction"] Ball_set[of P wellformed_transaction]
            admissible_transaction_is_wellformed_transaction(1)
      by blast
    ultimately have "((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>, Fun (Set s) S) \<notin> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)" for S
      using reachable_constraints_db\<^sub>l\<^sub>s\<^sub>s\<^sub>t_set_args_empty[OF \<A>_reach] 
      unfolding admissible_transaction_updates_def
      by auto
    thus "\<exists>ss. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = absc ss \<and> s \<notin> ss"
      using to_abs_alt_def[of "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>"] 4[of y] y y_val by auto
  qed

  show ?F
  proof (intro ballI impI)
    fix y assume y: "y \<in> fv_transaction T - set (transaction_fresh T)" "\<Gamma>\<^sub>v y = TAtom Value"
    then obtain yn where yn: "?\<theta> y \<cdot> \<I> = Fun (Val yn) []" using 4 by moura
    hence y_abs: "?\<theta> y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) = Fun (Abs (\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) yn)) []" by simp

    have "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<or> (y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<and>
          (\<exists>t s. select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_checks T)) \<and> y \<in> fv t \<union> fv s))"
      using admissible_transaction_fv_in_receives_or_selects[OF T_adm] y by blast
    thus "?\<theta> y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<in> absc ` set OCC"
    proof
      assume "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
      then obtain ts where ts:
          "receive\<langle>ts\<rangle> \<in> set (unlabel (transaction_receive T))" "y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set ts)"
        using wellformed_transaction_unlabel_cases(1)[OF T_wf]
        by (force simp add: unlabel_def)
      
      have *: "?\<theta> y \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set ts \<cdot>\<^sub>s\<^sub>e\<^sub>t ?\<theta> \<circ>\<^sub>s \<I>)"
              "list_all (\<lambda>t. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t \<cdot> ?\<theta> \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)) ts"
        using ts fv_subterms_substI[of y _ "?\<theta> \<circ>\<^sub>s \<I>"] subst_compose[of ?\<theta> \<I> y]
              subterms_subst_subset[of "?\<theta> \<circ>\<^sub>s \<I>"] receives_covered
        unfolding intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI, symmetric] list_all_iff
        by fastforce+

      have "Abs (\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) yn) \<in> \<Union>(funs_term ` (timpl_closure_set (set FP) (set TI)))"
        using * y_abs abs_subterms_in[of "?\<theta> y \<cdot> \<I>" _ "\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"]
              ideduct_synth_priv_fun_in_ik[
                OF _ funs_term_Fun_subterm'[of "Abs (\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) yn)" "[]"]]
        unfolding list_all_iff by fastforce
      hence "?\<theta> y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) \<in> subterms\<^sub>s\<^sub>e\<^sub>t (timpl_closure_set (set FP) (set TI))"
        using y_abs wf_trms_subterms[OF timpl_closure_set_wf_trms[OF FP(2), of "set TI"]]
              funs_term_Fun_subterm[of "Abs (\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>) yn)"]
        unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by fastforce
      hence "funs_term (?\<theta> y \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>))
              \<subseteq> (\<Union>t \<in> timpl_closure_set (set FP) (set TI). funs_term t)"
        using funs_term_subterms_eq(2)[of "timpl_closure_set (set FP) (set TI)"] by blast
      thus ?thesis using y_abs OCC(1) by fastforce
    next
      assume "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<and>
          (\<exists>t s. select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_checks T)) \<and> y \<in> fv t \<union> fv s)"
      then obtain t t' where
          "select\<langle>t,t'\<rangle> \<in> set (unlabel (transaction_checks T))" "y \<in> fv t \<union> fv t'"
        by blast
      then obtain l s where "(l,select\<langle>Var y, Fun (Set s) []\<rangle>) \<in> set (transaction_checks T)"
        using admissible_transaction_strand_step_cases(2)[OF T_adm]
        unfolding unlabel_def by fastforce
      then obtain U where U:
          "prefix (U@[(l,select\<langle>Var y, Fun (Set s) []\<rangle>)]) (transaction_checks T)"
        using in_set_conv_decomp[of "(l, select\<langle>Var y,Fun (Set s) []\<rangle>)" "transaction_checks T"]
        by (auto simp add: prefix_def)
      hence "select\<langle>Var y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))"
        by (force simp add: prefix_def unlabel_def)
      hence "select\<langle>?\<theta> y, Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t ?\<theta>))"
        using subst_lsst_unlabel_member
        by fastforce
      hence "(Fun (Val yn) [], Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
        using yn wellformed_transaction_sem_pos_checks[
                OF T_wf \<I>_is_T_model, of Assign "?\<theta> y" "Fun (Set s) []"]
        by fastforce
      hence "Fun (Val yn) [] \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
        using db\<^sub>s\<^sub>s\<^sub>t_in_cases[of "Fun (Val yn) []"]
        by (fastforce simp add: db\<^sub>s\<^sub>s\<^sub>t_def)
      thus ?thesis
        using OCC(3) yn abs_in[of "Fun (Val yn) []" _ "\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"]
        unfolding abs_value_constants_def
        by (metis (mono_tags, lifting) mem_Collect_eq subsetCE) 
    qed
  qed
qed

lemma transaction_prop4:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and P: "\<forall>T \<in> set P. admissible_transaction T"
    and x: "x \<in> set (transaction_fresh T)"
    and y: "y \<in> fv_transaction T - set (transaction_fresh T)" "\<Gamma>\<^sub>v y = TAtom Value"
  shows "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))" (is ?A)
    and "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))" (is ?B)
proof -
  let ?T' = "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"

  from \<I> have \<I>': "welltyped_constraint_model \<I> \<A>"
    using welltyped_constraint_model_prefix by auto

  have T_P_addm: "admissible_transaction T'" when T': "T' \<in> set P " for T'
    by (meson T' P)

  have T_adm: "admissible_transaction T"
    by (metis (full_types) P T)

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  have be: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
    using T_P_addm \<A>_reach reachable_constraints_no_bvars admissible_transaction_no_bvars(2)
    by blast

  have T_no_bvars: "fv_transaction T = vars_transaction T"
    using admissible_transaction_no_bvars[OF T_adm] by simp

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T_adm \<xi>]

  have \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" by (metis \<I> welltyped_constraint_model_def)

  have x_val: "fst x = TAtom Value"
    using x admissible_transactionE(14)[OF T_adm] unfolding list_all_iff by blast

  obtain xn where xn: "\<sigma> x = Fun (Val xn) []"
    using x_val transaction_fresh_subst_sends_to_val[OF \<sigma> x] \<Gamma>\<^sub>v_TAtom''(2)[of x] by meson
  hence xnxn: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x = Fun (Val xn) []"
    unfolding subst_compose_def \<xi>_empty by auto

  from xn xnxn have a0: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> = Fun (Val xn) []"
    by auto

  have b0: "\<Gamma>\<^sub>v x = TAtom Value"
    using P x T protocol_transaction_vars_TAtom_typed(3)
    by metis

  note 0 = a0 b0

  have \<sigma>_x_nin_A: "\<sigma> x \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
  proof -
    have "\<sigma> x \<in> subst_range \<sigma>"
      by (metis transaction_fresh_subst_sends_to_val[OF \<sigma> x b0])
    moreover
    have "(\<forall>t \<in> subst_range \<sigma>. t \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>))"
      using \<sigma> transaction_fresh_subst_def[of \<sigma> T \<A>] by auto
    ultimately
    show ?thesis
      by auto
  qed

  have *: "y \<notin> set (transaction_fresh T)"
     using assms by auto

  have **: "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T) \<or> (y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<and>
            (\<exists>t s. select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_checks T)) \<and> y \<in> fv t \<union> fv s))"
    using * y admissible_transaction_fv_in_receives_or_selects[OF T_adm]
    by blast

  have y_fv: "y \<in> fv_transaction T" using y fv_transaction_unfold by blast
  
  have y_val: "fst y = TAtom Value" using y(2) \<Gamma>\<^sub>v_TAtom''(2) by blast

  have "\<sigma> x \<cdot> \<I> \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))"
  proof (rule ccontr)
    assume "\<not>\<sigma> x \<cdot> \<I> \<notin> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))"
    then have a: "\<sigma> x \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))"
      by auto

    then have \<sigma>_x_I_in_A: "\<sigma> x \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      using reachable_constraints_subterms_subst[OF \<A>_reach \<I>' P] by blast

    have "\<exists>u. u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<and> \<I> u = \<sigma> x"
    proof -
      from \<sigma>_x_I_in_A have "\<exists>tu. tu \<in> \<Union> (subterms ` (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<and> tu \<cdot> \<I> = \<sigma> x \<cdot> \<I>"
        by force
      then obtain tu where tu: "tu \<in> \<Union> (subterms ` (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<and> tu \<cdot> \<I> = \<sigma> x \<cdot> \<I>"
        by auto
      then have "tu \<noteq> \<sigma> x"
        using \<sigma>_x_nin_A by auto
      moreover
      have "tu \<cdot> \<I> = \<sigma> x"
        using tu by (simp add: xn)
      ultimately
      have "\<exists>u. tu = Var u"
        unfolding xn by (cases tu) auto
      then obtain u where "tu = Var u"
        by auto
      have "u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<and> \<I> u = \<sigma> x"
      proof -
        have "u \<in> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
          using \<open>tu = Var u\<close> tu var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t by fastforce 
        then have "u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>"
          using be vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"] by blast
        moreover
        have "\<I> u = \<sigma> x"
          using \<open>tu = Var u\<close> \<open>tu \<cdot> \<I> = \<sigma> x\<close> by auto
        ultimately
        show ?thesis
          by auto
      qed
      then show "\<exists>u. u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<and> \<I> u = \<sigma> x"
        by metis
    qed
    then obtain u where u:
      "u \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" "\<I> u = \<sigma> x"
      by auto
    then have u_TA: "\<Gamma>\<^sub>v u = TAtom Value"
      using P(1) T x_val \<Gamma>\<^sub>v_TAtom''(2)[of x]
            wt_subst_trm''[OF \<I>_wt, of "Var u"] wt_subst_trm''[of \<sigma> "Var x"] 
            transaction_fresh_subst_wt[OF \<sigma>] protocol_transaction_vars_TAtom_typed(3)
      by force
    have "\<exists>B. prefix B \<A> \<and> u \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<and> \<I> u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      using u u_TA
      by (metis welltyped_constraint_model_prefix[OF \<I>]
                constraint_model_Value_var_in_constr_prefix[OF \<A>_reach _ P])
    then obtain B where "prefix B \<A> \<and> u \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<and> \<I> u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t B)"
      by blast
    moreover have "\<Union>(subterms ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t xs) \<subseteq> \<Union>(subterms ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t ys)"
      when "prefix xs ys"
      for xs ys::"('fun,'atom,'sets,'lbl) prot_strand"
      using that subterms\<^sub>s\<^sub>e\<^sub>t_mono trms\<^sub>s\<^sub>s\<^sub>t_mono unlabel_mono set_mono_prefix by metis
    ultimately have "\<I> u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      by blast
    then have "\<sigma> x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      using u by auto
    then show "False"
      using \<sigma>_x_nin_A by auto
  qed
  then show ?A
    using subst_apply_term.simps(1)[of x \<sigma>]
    unfolding subst_compose_def xn \<xi>_empty by auto

  from ** show ?B
  proof
    define T' where "T' \<equiv> transaction_receive T"
    define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

    assume y: "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
    hence "Var y \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')" by (metis T'_def fv\<^sub>s\<^sub>s\<^sub>t_is_subterm_trms\<^sub>s\<^sub>s\<^sub>t)
    then obtain z where z: "z \<in> set (unlabel T')" "Var y \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p z)"
      by (induct T') auto

    have "is_Receive z"
      using Ball_set[of "unlabel T'" is_Receive] z(1)
            admissible_transaction_is_wellformed_transaction(1)[OF T_adm]
      unfolding wellformed_transaction_def T'_def
      by blast
    then obtain tys where "z = receive\<langle>tys\<rangle>" by (cases z) auto
    hence tys: "receive\<langle>tys \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle> \<in> set (unlabel (T' \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))" "\<theta> y \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set tys \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
      using z subst_mono unfolding subst_apply_labeled_stateful_strand_def unlabel_def by force+
    hence y_deduct: "list_all (\<lambda>t. ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> t \<cdot> \<theta> \<cdot> \<I>) tys"
      using transaction_receive_deduct[OF T_wf _ \<xi> \<sigma> \<alpha>] \<I>
      unfolding T'_def \<theta>_def welltyped_constraint_model_def list_all_iff by auto

    obtain ty where ty: "ty \<in> set tys" "\<theta> y \<sqsubseteq> ty \<cdot> \<theta>" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> ty \<cdot> \<theta> \<cdot> \<I>"
      using tys y_deduct unfolding list_all_iff by blast

    obtain zn where zn: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val zn) []"
      using transaction_var_becomes_Val[
              OF reachable_constraints.step[OF \<A>_reach T \<xi> \<sigma> \<alpha>] \<I> \<xi> \<sigma> \<alpha> P T y_fv y_val]
      by metis

    have "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)"
      using ty tys(2) y_deduct private_fun_deduct_in_ik[of _ _ "Val zn"]
      by (metis \<theta>_def zn subst_mono public.simps(3))
    thus ?B
      using ik\<^sub>s\<^sub>s\<^sub>t_subst[of "unlabel \<A>" \<I>] unlabel_subst[of \<A> \<I>]
            subterms\<^sub>s\<^sub>e\<^sub>t_mono[OF ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset[of "unlabel (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>)"]]
      by fastforce
  next
    assume y': "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_checks T) \<and>
                (\<exists>t s. select\<langle>t,s\<rangle> \<in> set (unlabel (transaction_checks T)) \<and> y \<in> fv t \<union> fv s)"
    then obtain s where s: "select\<langle>Var y,s\<rangle> \<in> set (unlabel (transaction_checks T))"
                           "fst y = TAtom Value"
      using admissible_transaction_strand_step_cases(1,2)[OF T_adm] by fastforce

    obtain z zn where zn: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y = Var z" "\<I> z = Fun (Val zn) []"
      using transaction_var_becomes_Val[
              OF reachable_constraints.step[OF \<A>_reach T \<xi> \<sigma> \<alpha>] \<I> \<xi> \<sigma> \<alpha> P T y_fv s(2)]
            transaction_decl_fresh_renaming_substs_range(4)[OF \<xi> \<sigma> \<alpha> _ *]
            transaction_decl_subst_empty_inv[OF \<xi>[unfolded \<xi>_empty]]
      by auto

    have transaction_selects_db_here:
        "\<And>n s. select\<langle>Var (TAtom Value, n), Fun (Set s) []\<rangle> \<in> set (unlabel (transaction_checks T))
                \<Longrightarrow> (\<alpha> (TAtom Value, n) \<cdot> \<I>, Fun (Set s) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using transaction_selects_db[OF T_adm _ \<xi> \<sigma> \<alpha>] \<I>
      unfolding welltyped_constraint_model_def by auto

    have "\<exists>n. y = (Var Value, n)"
      using T \<Gamma>\<^sub>v_TAtom_inv(2) y_fv y(2)
      by blast
    moreover
    have "admissible_transaction_checks T"
      using admissible_transaction_is_wellformed_transaction(2)[OF T_adm]
      by blast
    then have "is_Fun_Set (the_set_term (select\<langle>Var y,s\<rangle>))"
      using s unfolding admissible_transaction_checks_def
      by auto
    then have "\<exists>ss. s = Fun (Set ss) []"
      using is_Fun_Set_exi
      by auto
    ultimately
    obtain n ss where nss: "y = (TAtom Value, n)" "s = Fun (Set ss) []"
      by auto
    then have "select\<langle>Var (TAtom Value, n), Fun (Set ss) []\<rangle> \<in> set (unlabel (transaction_checks T))"
      using s by auto
    then have in_db: "(\<alpha> (TAtom Value, n) \<cdot> \<I>, Fun (Set ss) []) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
      using transaction_selects_db_here[of n ss] by auto
    have "(\<I> z, s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
    proof -
      have "(\<alpha> y \<cdot> \<I>, s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
        using in_db nss by auto
      moreover 
      have "\<alpha> y = Var z"
        using zn \<xi>_empty * \<sigma>
        by (metis (no_types, opaque_lifting) subst_compose_def subst_imgI subst_to_var_is_var
                  term.distinct(1) transaction_fresh_subst_def var_comp(2)) 
      then have "\<alpha> y \<cdot> \<I> = \<I> z"
        by auto
      ultimately
      show "(\<I> z, s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
        by auto
    qed
    then have "\<exists>t' s'. insert\<langle>t',s'\<rangle> \<in> set (unlabel \<A>) \<and> \<I> z = t' \<cdot> \<I> \<and> s = s' \<cdot> \<I>"
      using db\<^sub>s\<^sub>s\<^sub>t_in_cases[of "\<I> z" s "unlabel \<A>" \<I> "[]"] unfolding db\<^sub>s\<^sub>s\<^sub>t_def by auto
    then obtain t' s' where t's': "insert\<langle>t',s'\<rangle> \<in> set (unlabel \<A>) \<and> \<I> z = t' \<cdot> \<I> \<and> s = s' \<cdot> \<I>"
      by auto
    then have "t' \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      by force
    then have "t' \<cdot> \<I> \<in> (subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      by auto
    then have "\<I> z \<in> (subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      using t's' by auto
    then have "\<I> z \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A> \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<I>))"
      using reachable_constraints_subterms_subst[
              OF \<A>_reach welltyped_constraint_model_prefix[OF \<I>] P]
      by auto
    then show ?B
      using zn(1) by simp
  qed
qed

lemma transaction_prop5:
  fixes T \<xi> \<sigma> \<alpha> \<A> \<I> T' a0 a0' \<theta>
  defines "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    and "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
    and "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') \<I>)"
    and "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@T')"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and step: "list_all (transaction_check (FP, OCC, TI)) P"
  shows "\<exists>\<delta> \<in> abs_substs_fun ` set (transaction_check_comp (\<lambda>_ _. True) (FP, OCC, TI) T).
         \<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
            (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x) \<and>
            (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' = absc (absdbupd (unlabel (transaction_updates T)) x (\<delta> x))"
proof -
  define comp0 where
    "comp0 \<equiv> abs_substs_fun ` set (transaction_check_comp (\<lambda>_ _. True) (FP, OCC, TI) T)"
  define check0 where "check0 \<equiv> transaction_check (FP, OCC, TI) T"
  define upd where "upd \<equiv> \<lambda>\<delta> x. absdbupd (unlabel (transaction_updates T)) x (\<delta> x)"
  define b0 where "b0 \<equiv> \<lambda>x. THE b. absc b = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0"

  note all_defs = comp0_def check0_def a0_def a0'_def upd_def b0_def \<theta>_def T'_def

  have \<A>_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
    by (metis reachable_constraints_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s admissible_transactions_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s P(1) \<A>_reach)

  have \<I>_interp: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
    and \<I>_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
    by (metis \<I> welltyped_constraint_model_def constraint_model_def,
        metis \<I> welltyped_constraint_model_def,
        metis \<I> welltyped_constraint_model_def constraint_model_def)

  have \<I>_is_T_model: "strand_sem_stateful (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) (set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)) (unlabel T') \<I>"
    using \<I> unlabel_append[of \<A> T'] db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>" \<I> "[]"]
          strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" "unlabel T'" \<I>]
    by (simp add: welltyped_constraint_model_def constraint_model_def db\<^sub>s\<^sub>s\<^sub>t_def)

  have T_adm: "admissible_transaction T"
    using T P(1) Ball_set[of P "admissible_transaction"]
    by blast

  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  have T_no_bvars: "fv_transaction T = vars_transaction T" "bvars_transaction T = {}"
    using admissible_transaction_no_bvars[OF T_adm] by simp_all

  have T_vars_const_typed: "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
    and T_fresh_vars_value_typed: "\<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
    using T P protocol_transaction_vars_TAtom_typed(2,3)[of T] by simp_all

  note \<xi>_empty = admissible_transaction_decl_subst_empty[OF T_adm \<xi>]

  have wt_\<sigma>\<alpha>\<I>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>)" and wt_\<sigma>\<alpha>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    using \<I>_wt wt_subst_compose transaction_decl_fresh_renaming_substs_wt[OF \<xi> \<sigma> \<alpha>]
    by (blast, blast)

  have T_vars_vals: "\<forall>x \<in> fv_transaction T. \<exists>n. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> = Fun (Val n) []"
  proof
    fix x assume x: "x \<in> fv_transaction T"
    have "\<exists>n. (\<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> = Fun (Val n) []"
    proof (cases "x \<in> subst_domain \<sigma>")
      case True
      then obtain n where "\<sigma> x = Fun (Val n) []"
        using transaction_fresh_subst_sends_to_val[OF \<sigma>]
              transaction_fresh_subst_domain[OF \<sigma>]
              T_fresh_vars_value_typed
        by metis
      thus ?thesis by (simp add: subst_compose_def)
    next
      case False
      hence *: "(\<sigma> \<circ>\<^sub>s \<alpha>) x = \<alpha> x" by (auto simp add: subst_compose_def)
      
      obtain y where y: "\<Gamma>\<^sub>v x = \<Gamma>\<^sub>v y" "\<alpha> x = Var y"
        using transaction_renaming_subst_wt[OF \<alpha>]
              transaction_renaming_subst_is_renaming(1)[OF \<alpha>]
        by (metis \<Gamma>.simps(1) prod.exhaust wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
      hence "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>)"
        using x * T_no_bvars(2) unlabel_subst[of "transaction_strand T" "\<sigma> \<circ>\<^sub>s \<alpha>"]
              fv\<^sub>s\<^sub>s\<^sub>t_subst_fv_subset[of x "unlabel (transaction_strand T)" "\<sigma> \<circ>\<^sub>s \<alpha>"]
        by auto
      hence "y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>))"
        using fv\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<sigma> \<circ>\<^sub>s \<alpha>"]
              fv\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] unlabel_append[of \<A>]
        by auto
      thus ?thesis
        using x y * T P (* T_vars_const_typed *)
              constraint_model_Value_term_is_Val[
                OF reachable_constraints.step[OF \<A>_reach T \<xi> \<sigma> \<alpha>] \<I>[unfolded T'_def] P(1), of y]
              admissible_transaction_Value_vars[of T] \<xi>_empty
        by simp
    qed
    thus "\<exists>n. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> = Fun (Val n) []" using \<xi>_empty by simp
  qed

  have T_vars_absc: "\<forall>x \<in> fv_transaction T. \<exists>!n. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc n"
    using T_vars_vals by fastforce
  hence "(absc \<circ> b0) x = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0" when "x \<in> fv_transaction T" for x
    using that unfolding b0_def by fastforce
  hence T_vars_absc': "t \<cdot> (absc \<circ> b0) = t \<cdot> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0"
    when "fv t \<subseteq> fv_transaction T" "\<nexists>n T. Fun (Val n) T \<in> subterms t" for t
    using that(1) abs_term_subst_eq'[OF _ that(2), of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>" a0 "absc \<circ> b0"]
          subst_compose[of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" \<I>] subst_subst_compose[of t "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" \<I>]
    by fastforce

  have "\<exists>\<delta> \<in> comp0. \<forall>x \<in> fv_transaction T. fst x = TAtom Value \<longrightarrow> b0 x = \<delta> x"
  proof -
    let ?C = "set (unlabel (transaction_checks T))"
    let ?xs = "fv_transaction T - set (transaction_fresh T)"

    note * = transaction_prop3[OF \<A>_reach T \<I>[unfolded T'_def] \<xi> \<sigma> \<alpha> FP OCC TI P(1)]

    have **:
        "\<forall>x \<in> set (transaction_fresh T). b0 x = {}"
        "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> b0)"
          (is ?B)
    proof -
      show ?B
      proof (intro ballI impI)
        fix t assume t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)"
        hence t': "fv t \<subseteq> fv_transaction T" "\<nexists>n T. Fun (Val n) T \<in> subterms t"
          using trms_transaction_unfold[of T] vars_transaction_unfold[of T]
                trms\<^sub>s\<^sub>s\<^sub>t_fv_vars\<^sub>s\<^sub>s\<^sub>t_subset[of t "unlabel (transaction_strand T)"]
                admissible_transactions_no_Value_consts'[OF T_adm]
                wellformed_transaction_send_receive_fv_subset(1)[OF T_wf t(1)]
          by blast+
        
        have "intruder_synth_mod_timpls FP TI (t \<cdot> (absc \<circ> b0))"
          using t(1) t' *(2) T_vars_absc'
          by (metis a0_def)
        moreover have "(absc \<circ> b0) x = (\<theta> b0) x" when "x \<in> fv t" for x
          using that T P admissible_transaction_Value_vars[of T]
                \<open>fv t \<subseteq> fv_transaction T\<close> \<Gamma>\<^sub>v_TAtom''(2)[of x]
          unfolding \<theta>_def by fastforce
        hence "t \<cdot> (absc \<circ> b0) = t \<cdot> \<theta> b0"
          using term_subst_eq[of t "absc \<circ> b0" "\<theta> b0"] by argo
        ultimately show "intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> b0)"
          using intruder_synth.simps[of "set FP"] by (cases "t \<cdot> \<theta> b0") metis+
      qed
    qed (simp add: *(1) a0_def b0_def)

    have ***: "\<forall>x \<in> ?xs. \<forall>s. select\<langle>Var x,Fun (Set s) []\<rangle> \<in> ?C \<longrightarrow> s \<in> b0 x"
              "\<forall>x \<in> ?xs. \<forall>s. \<langle>Var x in Fun (Set s) []\<rangle> \<in> ?C \<longrightarrow> s \<in> b0 x"
              "\<forall>x \<in> ?xs. \<forall>s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> ?C \<longrightarrow> s \<notin> b0 x"
              "\<forall>x \<in> ?xs. fst x = TAtom Value \<longrightarrow> b0 x \<in> set OCC"
      unfolding a0_def b0_def
      using *(3,4) apply (force, force)
      using *(5) apply force
      using *(6) admissible_transaction_Value_vars[OF bspec[OF P T]] by force

    show ?thesis
      using transaction_check_comp_in[OF T_adm **[unfolded \<theta>_def] ***]
      unfolding comp0_def
      by metis
  qed
  hence 1: "\<exists>\<delta> \<in> comp0. \<forall>x \<in> fv_transaction T.
              fst x = TAtom Value \<longrightarrow> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x)"
    using T_vars_absc unfolding b0_def a0_def by fastforce

  obtain \<delta> where \<delta>:
      "\<delta> \<in> comp0" "\<forall>x \<in> fv_transaction T. fst x = TAtom Value \<longrightarrow> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x)"
    using 1 by moura

  have 2: "\<theta> x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) = absc (absdbupd (unlabel A) x d)"
    when "\<theta> x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 D = absc d"
    and "\<forall>t u. insert\<langle>t,u\<rangle> \<in> set (unlabel A) \<longrightarrow> (\<exists>y s. t = Var y \<and> u = Fun (Set s) [])"
    and "\<forall>t u. delete\<langle>t,u\<rangle> \<in> set (unlabel A) \<longrightarrow> (\<exists>y s. t = Var y \<and> u = Fun (Set s) [])"
    and "\<forall>y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<theta> x \<cdot> \<I> = \<theta> y \<cdot> \<I> \<longrightarrow> x = y"
    and "\<forall>y \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<exists>n. \<theta> y \<cdot> \<I> = Fun (Val n) []"
    and x: "\<theta> x \<cdot> \<I> = Fun (Val n) []"
    and D: "\<forall>d \<in> set D. \<exists>s. snd d = Fun (Set s) []"
    for A::"('fun,'atom,'sets,'lbl) prot_strand" and x \<theta> D n d
    using that(2,3,4,5)
  proof (induction A rule: List.rev_induct)
    case (snoc a A)
    then obtain l b where a: "a = (l,b)" by (metis surj_pair)

    have IH: "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n = absdbupd (unlabel A) x d"
      using snoc unlabel_append[of A "[a]"] a x
      by (simp del: unlabel_append)

    have b_prems: "\<forall>y \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p b. \<theta> x \<cdot> \<I> = \<theta> y \<cdot> \<I> \<longrightarrow> x = y"
                  "\<forall>y \<in> fv\<^sub>s\<^sub>s\<^sub>t\<^sub>p b. \<exists>n. \<theta> y \<cdot> \<I> = Fun (Val n) []"
      using snoc.prems(3,4) a by (simp_all add: unlabel_def)

    have *: "filter is_Update (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))) =
             filter is_Update (unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)))"
            "filter is_Update (unlabel (A@[a])) = filter is_Update (unlabel A)"
      when "\<not>is_Update b"
      using that a
      by (cases b, simp_all add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def unlabel_def subst_apply_labeled_stateful_strand_def)+

    note ** = IH a dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_append[of A "[a]" \<theta>]

    note *** = * absdbupd_filter[of "unlabel (A@[a])"]
               absdbupd_filter[of "unlabel A"]
               db\<^sub>s\<^sub>s\<^sub>t_filter[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"]
               db\<^sub>s\<^sub>s\<^sub>t_filter[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>))"]

    note **** = **(2,3) dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst_snoc[of A a \<theta>]
                unlabel_append[of "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>" "[dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]"]
                db\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)" "unlabel [dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>]" \<I> D]

    have "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n = absdbupd (unlabel (A@[a])) x d" using ** ***
    proof (cases b)
      case (Insert t t')
      then obtain y s m where y: "t = Var y" "t' = Fun (Set s) []" "\<theta> y \<cdot> \<I> = Fun (Val m) []"
        using snoc.prems(1) b_prems(2) a by (fastforce simp add: unlabel_def)
      hence a': "db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D =
                 List.insert ((Fun (Val m) [], Fun (Set s) [])) (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D)"
                "unlabel [dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>] = [insert\<langle>\<theta> y, Fun (Set s) []\<rangle>]"
                "unlabel [a] = [insert\<langle>Var y, Fun (Set s) []\<rangle>]"
        using **** Insert by simp_all

      show ?thesis
      proof (cases "x = y")
        case True
        hence "\<theta> x \<cdot> \<I> = \<theta> y \<cdot> \<I>" by simp
        hence "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n =
               insert s (\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n)"
          by (metis (no_types, lifting) y(3) a'(1) x dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst to_abs_list_insert')
        thus ?thesis using True IH a'(3) absdbupd_append[of "unlabel A"] by (simp add: unlabel_def)
      next
        case False
        hence "\<theta> x \<cdot> \<I> \<noteq> \<theta> y \<cdot> \<I>" using b_prems(1) y Insert by simp
        hence "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n = \<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n"
          by (metis (no_types, lifting) y(3) a'(1) x dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst to_abs_list_insert)
        thus ?thesis using False IH a'(3) absdbupd_append[of "unlabel A"] by (simp add: unlabel_def)
      qed
    next
      case (Delete t t')
      then obtain y s m where y: "t = Var y" "t' = Fun (Set s) []" "\<theta> y \<cdot> \<I> = Fun (Val m) []"
        using snoc.prems(2) b_prems(2) a by (fastforce simp add: unlabel_def)
      hence a': "db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D =
                 List.removeAll ((Fun (Val m) [], Fun (Set s) [])) (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D)"
                "unlabel [dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<theta>] = [delete\<langle>\<theta> y, Fun (Set s) []\<rangle>]"
                "unlabel [a] = [delete\<langle>Var y, Fun (Set s) []\<rangle>]"
        using **** Delete by simp_all

      have "\<exists>s S. snd d = Fun (Set s) []" when "d \<in> set (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D)" for d
        using snoc.prems(1,2) db\<^sub>l\<^sub>s\<^sub>s\<^sub>t_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_set_ex[OF that _ _ D] by (simp add: unlabel_def)
      moreover {
        fix t::"('fun,'atom,'sets,'lbl) prot_term"
          and D::"(('fun,'atom,'sets,'lbl) prot_term \<times> ('fun,'atom,'sets,'lbl) prot_term) list"
        assume "\<forall>d \<in> set D. \<exists>s. snd d = Fun (Set s) []"
        hence "removeAll (t, Fun (Set s) []) D = filter (\<lambda>d. \<nexists>S. d = (t, Fun (Set s) S)) D"
          by (induct D) auto
      } ultimately have a'':
          "List.removeAll ((Fun (Val m) [], Fun (Set s) [])) (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D) =
           filter (\<lambda>d. \<nexists>S. d = (Fun (Val m) [], Fun (Set s) S)) (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>) \<I> D)"
        by simp

      show ?thesis
      proof (cases "x = y")
        case True
        hence "\<theta> x \<cdot> \<I> = \<theta> y \<cdot> \<I>" by simp
        hence "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n =
               (\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n) - {s}"
          using y(3) a'' a'(1) x by (simp add: dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst to_abs_list_remove_all')
        thus ?thesis using True IH a'(3) absdbupd_append[of "unlabel A"] by (simp add: unlabel_def)
      next
        case False
        hence "\<theta> x \<cdot> \<I> \<noteq> \<theta> y \<cdot> \<I>" using b_prems(1) y Delete by simp
        hence "\<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[a] \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n = \<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>)) \<I> D) n"
          by (metis (no_types, lifting) y(3) a'(1) x dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_subst to_abs_list_remove_all)
        thus ?thesis using False IH a'(3) absdbupd_append[of "unlabel A"] by (simp add: unlabel_def)
      qed
    qed simp_all
    thus ?case by (simp add: x)
  qed (simp add: that(1))

  have 3: "x = y"
    when xy: "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I>" "x \<in> fv_transaction T" "y \<in> fv_transaction T"
    for x y
  proof -
    have "x \<notin> set (transaction_fresh T) \<Longrightarrow> y \<notin> set (transaction_fresh T) \<Longrightarrow> ?thesis"
      using xy admissible_transaction_strand_sem_fv_ineq[OF T_adm \<I>_is_T_model[unfolded T'_def]]
      by fast
    moreover {
      assume *: "x \<in> set (transaction_fresh T)" "y \<in> set (transaction_fresh T)"
      hence "\<Gamma>\<^sub>v x = TAtom Value" "\<Gamma>\<^sub>v y = TAtom Value"
        using T_fresh_vars_value_typed by (blast, blast)
      then obtain xn yn where "\<sigma> x = Fun (Val xn) []" "\<sigma> y = Fun (Val yn) []"
        using * transaction_fresh_subst_sends_to_val[OF \<sigma>] by meson
      hence "\<sigma> x = \<sigma> y" using that(1) \<xi>_empty by (simp add: subst_compose)
      moreover have "inj_on \<sigma> (subst_domain \<sigma>)" "x \<in> subst_domain \<sigma>" "y \<in> subst_domain \<sigma>"
        using * \<sigma> unfolding transaction_fresh_subst_def by auto
      ultimately have ?thesis unfolding inj_on_def by blast
    } moreover have False when "x \<in> set (transaction_fresh T)" "y \<notin> set (transaction_fresh T)"
      using that(2) xy T_no_bvars admissible_transaction_Value_vars[OF bspec[OF P T], of y]
            transaction_prop4[OF \<A>_reach T \<I>[unfolded T'_def] \<xi> \<sigma> \<alpha> P that(1), of y]
      by auto
    moreover have False when "x \<notin> set (transaction_fresh T)" "y \<in> set (transaction_fresh T)"
      using that(1) xy T_no_bvars admissible_transaction_Value_vars[OF bspec[OF P T], of x]
            transaction_prop4[OF \<A>_reach T \<I>[unfolded T'_def] \<xi> \<sigma> \<alpha> P that(2), of x]
      by fastforce
    ultimately show ?thesis by metis
  qed

  have 4: "\<exists>y s. t = Var y \<and> u = Fun (Set s) []"
    when "insert\<langle>t,u\<rangle> \<in> set (unlabel (transaction_strand T))" for t u
    using that admissible_transaction_strand_step_cases(3)[OF T_adm] T_wf
    by blast

  have 5: "\<exists>y s. t = Var y \<and> u = Fun (Set s) []"
    when "delete\<langle>t,u\<rangle> \<in> set (unlabel (transaction_strand T))" for t u
    using that admissible_transaction_strand_step_cases(3)[OF T_adm] T_wf
    by blast

  have 6: "\<exists>n. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) y \<cdot> \<I> = Fun (Val n) []" when "y \<in> fv_transaction T" for y
    using that by (simp add: T_vars_vals)

  have "list_all wellformed_transaction P" "list_all admissible_transaction_updates P"
    using P(1) Ball_set[of P "admissible_transaction"] Ball_set[of P wellformed_transaction]
          Ball_set[of P admissible_transaction_updates]
          admissible_transaction_is_wellformed_transaction(1,3)
    by fastforce+
  hence 7: "\<exists>s. snd d = Fun (Set s) []" when "d \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)" for d
    using that reachable_constraints_db\<^sub>l\<^sub>s\<^sub>s\<^sub>t_set_args_empty[OF \<A>_reach]
    unfolding admissible_transaction_updates_def by (cases d) simp

  have "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' = absc (upd \<delta> x)"
    when x: "x \<in> fv_transaction T" "fst x = TAtom Value" for x
  proof -
    have "(\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 (db'\<^sub>l\<^sub>s\<^sub>s\<^sub>t (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<I> (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>))
           = absc (absdbupd (unlabel (transaction_strand T)) x (\<delta> x))"
      using 2[of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" x "db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>" "\<delta> x" "transaction_strand T"]
            3[OF _ x(1)] 4 5 6[OF that(1)] 6 7 x \<delta>(2)
      unfolding all_defs by blast
    thus ?thesis
      using x db\<^sub>s\<^sub>s\<^sub>t_append[of "unlabel \<A>"] absdbupd_wellformed_transaction[OF T_wf]
      unfolding all_defs db\<^sub>s\<^sub>s\<^sub>t_def by force
  qed
  thus ?thesis using \<delta> \<Gamma>\<^sub>v_TAtom''(2) unfolding all_defs by blast
qed

lemma transaction_prop6:
  fixes T \<xi> \<sigma> \<alpha> \<A> \<I> T' a0 a0'
  defines "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    and "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
    and "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') \<I>)"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@T')"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and step: "list_all (transaction_check (FP, OCC, TI)) P"
  shows "\<forall>t \<in> timpl_closure_set (\<alpha>\<^sub>i\<^sub>k \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>).
          timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t" (is ?A)
    and "timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>) \<subseteq> absc ` set OCC" (is ?B)
    and "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T). is_Fun (t \<cdot> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0') \<longrightarrow>
          timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t \<cdot> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'" (is ?C)
    and "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
          (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> absc ` set OCC" (is ?D)
proof -
  define comp0 where
    "comp0 \<equiv> abs_substs_fun ` set (transaction_check_comp (\<lambda>_ _. True) (FP, OCC, TI) T)"
  define check0 where "check0 \<equiv> transaction_check (FP, OCC, TI) T"

  define upd where "upd \<equiv> \<lambda>\<delta> x. absdbupd (unlabel (transaction_updates T)) x (\<delta> x)"

  define \<theta> where "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"

  have T_adm: "admissible_transaction T" using T P(1) by metis
  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  have \<theta>_prop: "\<theta> \<sigma> x = absc (\<sigma> x)" when "\<Gamma>\<^sub>v x = TAtom Value" for \<sigma> x
    using that \<Gamma>\<^sub>v_TAtom''(2)[of x] unfolding \<theta>_def by simp

  (* The set-membership status of all value constants in T under \<I>, \<sigma>, \<alpha> are covered by the check *)
  have 0: "\<exists>\<delta> \<in> comp0. \<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
            (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x) \<and>
            (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' = absc (upd \<delta> x)"
    using transaction_prop5[OF \<A>_reach T \<I>[unfolded T'_def] \<xi> \<sigma> \<alpha> FP OCC TI P step]
    unfolding a0_def a0'_def T'_def upd_def comp0_def
    by blast

  (* All set-membership changes are covered by the term implication graph *)
  have 1: "(\<delta> x, upd \<delta> x) \<in> (set TI)\<^sup>+"
    when "\<delta> \<in> comp0" "\<delta> x \<noteq> upd \<delta> x" "x \<in> fv_transaction T" "x \<notin> set (transaction_fresh T)"
    for x \<delta> 
    using T that step Ball_set[of P "transaction_check (FP, OCC, TI)"]
          transaction_prop1[of \<delta> "\<lambda>_ _. True" FP OCC TI T x] TI
    unfolding upd_def comp0_def transaction_check_def
    by blast

  (* All set-membership changes are covered by the fixed point *)
  have 2: (* "\<delta> x \<in> set OCC" *) "upd \<delta> x \<in> set OCC"
    when "\<delta> \<in> comp0" "x \<in> fv_transaction T" "fst x = TAtom Value" for x \<delta>
    using T that step Ball_set[of P "transaction_check (FP, OCC, TI)"]
          T_adm FP OCC TI transaction_prop2[of \<delta> "\<lambda>_ _. True" FP OCC TI T x]
    unfolding upd_def comp0_def transaction_check_def
    by blast
  
  obtain \<delta> where \<delta>:
      "\<delta> \<in> comp0"
      "\<forall>x \<in> fv_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<longrightarrow>
        (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 = absc (\<delta> x) \<and>
        (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' = absc (upd \<delta> x)"
    using 0 by moura

  have "\<exists>x. ab = (\<delta> x, upd \<delta> x) \<and> x \<in> fv_transaction T - set (transaction_fresh T) \<and> \<delta> x \<noteq> upd \<delta> x"
    when ab: "ab \<in> \<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>" for ab
  proof -
    obtain a b where ab': "ab = (a,b)" by (metis surj_pair)
    then obtain x where x:
        "a \<noteq> b" "x \<in> fv_transaction T" "x \<notin> set (transaction_fresh T)"
        "absc a = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0" "absc b = (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) x \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0'"
      using ab unfolding abs_term_implications_def a0_def a0'_def T'_def by blast
    hence "absc a = absc (\<delta> x)" "absc b = absc (upd \<delta> x)"
      using \<delta>(2) admissible_transaction_Value_vars[OF bspec[OF P T] x(2)]
      by metis+
    thus ?thesis using x ab' by blast
  qed
  hence \<alpha>\<^sub>t\<^sub>i_TI_subset: "\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I> \<subseteq> {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}" using 1[OF \<delta>(1)] by blast
  
  have "timpl_closure_set (timpl_closure_set (set FP) (set TI)) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>) \<turnstile>\<^sub>c t"
    when t: "t \<in> timpl_closure_set (\<alpha>\<^sub>i\<^sub>k \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>)" for t
    using timpl_closure_set_is_timpl_closure_union[of "\<alpha>\<^sub>i\<^sub>k \<A> \<I>" "\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>"]
          intruder_synth_timpl_closure_set FP(3) t
    by blast
  thus ?A
    using ideduct_synth_mono[OF _ timpl_closure_set_mono[OF
            subset_refl[of "timpl_closure_set (set FP) (set TI)"]
            \<alpha>\<^sub>t\<^sub>i_TI_subset]]
          timpl_closure_set_timpls_trancl_eq'[of "timpl_closure_set (set FP) (set TI)" "set TI"]
    unfolding timpl_closure_set_idem
    by force

  have "timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>) \<subseteq>
        timpl_closure_set (absc ` set OCC) {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    using timpl_closure_set_mono[OF _ \<alpha>\<^sub>t\<^sub>i_TI_subset] OCC(3) by blast
  thus ?B using OCC(2) timpl_closure_set_timpls_trancl_subset' by blast

  have "transaction_check_post (FP, OCC, TI) T \<delta>"
    using T \<delta>(1) step
    unfolding transaction_check_def transaction_check'_def comp0_def list_all_iff
    by fastforce
  hence 3: "timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t \<cdot> \<theta> (upd \<delta>)"
    when "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "is_Fun (t \<cdot> \<theta> (upd \<delta>))" for t
    using that
    unfolding transaction_check_post_def upd_def \<theta>_def
              intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI, symmetric]
    by fastforce

  have 4: "\<forall>x \<in> fv t. (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>) x \<cdot>\<^sub>\<alpha> a0' = \<theta> (upd \<delta>) x"
    when "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" for t
    using wellformed_transaction_send_receive_fv_subset(2)[OF T_wf that]
          \<delta>(2) subst_compose[of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" \<I>] \<theta>_prop
          admissible_transaction_Value_vars[OF bspec[OF P T]]
    by fastforce
  
  have 5: "\<nexists>n T. Fun (Val n) T \<in> subterms t" when "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" for t
    using that admissible_transactions_no_Value_consts'[OF T_adm] trms_transaction_unfold[of T]
    by blast

  show ?D using 2[OF \<delta>(1)] \<delta>(2) \<Gamma>\<^sub>v_TAtom''(2) unfolding a0'_def T'_def by blast

  show ?C using 3 abs_term_subst_eq'[OF 4 5] by simp
qed

lemma reachable_constraints_covered_step:
  fixes \<A>::"('fun,'atom,'sets,'lbl) prot_constr"
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and T: "T \<in> set P"
    and \<I>: "welltyped_constraint_model \<I> (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>))"
    and \<xi>: "transaction_decl_subst \<xi> T"
    and \<sigma>: "transaction_fresh_subst \<sigma> T \<A>"
    and \<alpha>: "transaction_renaming_subst \<alpha> P \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
      "ground (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and transactions_covered: "list_all (transaction_check (FP, OCC, TI)) P"
  shows "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<I>.
          timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t" (is ?A)
    and "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s (\<A>@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) \<I> \<subseteq> absc ` set OCC" (is ?B)
proof -
  note step_props = transaction_prop6[OF \<A>_reach T \<I> \<xi> \<sigma> \<alpha> FP(1,2,3) OCC TI P transactions_covered]

  define T' where "T' \<equiv> dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  define a0 where "a0 \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)"
  define a0' where "a0' \<equiv> \<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t (\<A>@T') \<I>)"

  define vals where "vals \<equiv> \<lambda>S::('fun,'atom,'sets,'lbl) prot_constr.
      {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>. \<exists>n. t = Fun (Val n) []}"

  define vals_sym where "vals_sym \<equiv> \<lambda>S::('fun,'atom,'sets,'lbl) prot_constr.
      {t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t S). (\<exists>n. t = Fun (Val n) []) \<or> (\<exists>m. t = Var (TAtom Value,m))}"

  have \<I>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" by (metis \<I> welltyped_constraint_model_def)

  have \<I>_grounds: "fv (t \<cdot> \<I>) = {}" for t
    using \<I> interpretation_grounds[of \<I>]
    unfolding welltyped_constraint_model_def constraint_model_def by auto

  have wt_\<sigma>\<alpha>\<I>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>)" and wt_\<sigma>\<alpha>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    using \<I>_wt wt_subst_compose transaction_decl_fresh_renaming_substs_wt[OF \<xi> \<sigma> \<alpha>]
    by (blast, blast)

  have "\<forall>T\<in>set P. bvars_transaction T = {}"
    using P admissible_transactionE(4) by metis
  hence \<A>_no_bvars: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> = {}"
    using reachable_constraints_no_bvars[OF \<A>_reach] by metis

  have \<I>_vals: "\<exists>n. \<I> (TAtom Value, m) = Fun (Val n) []"
    when "(TAtom Value, m) \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" for m
    using constraint_model_Value_term_is_Val'[
            OF \<A>_reach welltyped_constraint_model_prefix[OF \<I>] P(1)]
          \<A>_no_bvars vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel \<A>"] that
    by blast

  have vals_sym_vals: "t \<cdot> \<I> \<in> vals \<A>" when t: "t \<in> vals_sym \<A>" for t
  proof (cases t)
    case (Var x)
    then obtain m where *: "x = (TAtom Value,m)" using t unfolding vals_sym_def by blast
    moreover have "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" using t unfolding vals_sym_def by blast
    hence "t \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "\<exists>n. \<I> (Var Value, m) = Fun (Val n) []"
      using Var * \<I>_vals[of m] var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t[of x "unlabel \<A>"]
            \<Gamma>\<^sub>v_TAtom[of Value m] reachable_constraints_Value_vars_are_fv[OF \<A>_reach P(1), of x]
      by blast+
    ultimately show ?thesis using Var unfolding vals_def by auto
  next
    case (Fun f T)
    then obtain n where "f = Val n" "T = []" using t unfolding vals_sym_def by blast
    moreover have "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" using t unfolding vals_sym_def by blast
    hence "t \<cdot> \<I> \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" using Fun by blast
    ultimately show ?thesis using Fun unfolding vals_def by auto
  qed

  have vals_vals_sym: "\<exists>s. s \<in> vals_sym \<A> \<and> t = s \<cdot> \<I>" when "t \<in> vals \<A>" for t
    using that constraint_model_Val_is_Value_term[OF \<I>]
    unfolding vals_def vals_sym_def by fast

  have T_adm: "admissible_transaction T" by (metis P(1) T)
  note T_wf = admissible_transaction_is_wellformed_transaction(1)[OF T_adm]

  have 0:
      "\<alpha>\<^sub>i\<^sub>k (\<A>@T') \<I> = (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0' \<union> (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
      "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s (\<A>@T') \<I> = vals \<A> \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0' \<union> vals T' \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    by (metis abs_intruder_knowledge_append a0'_def,
        metis abs_value_constants_append[of \<A> T' \<I>] a0'_def vals_def)

  have 1: "(ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t T' \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0' =
           (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    by (metis T'_def dual_transaction_ik_is_transaction_send''[OF T_wf])

  have 2: "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<inter> subst_domain \<xi> = {}"
          "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<inter> subst_domain \<sigma> = {}"
          "bvars\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T) \<inter> subst_domain \<alpha> = {}"
    using admissible_transactionE(4)[OF T_adm] by blast+

  have "vals T' \<subseteq> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` fv_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
  proof
    fix t assume "t \<in> vals T'"
    then obtain s n where s:
        "s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t T')" "t = s \<cdot> \<I>" "t = Fun (Val n) []"
      unfolding vals_def by fast
    then obtain u where u:
        "u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T))"
        "s = u \<cdot> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
      using transaction_decl_fresh_renaming_substs_trms[OF \<xi> \<sigma> \<alpha> 2]
            trms\<^sub>s\<^sub>s\<^sub>t_unlabel_dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_eq[of "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
      unfolding T'_def by blast

    have *: "t = u \<cdot> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s \<I>)" by (metis subst_subst_compose s(2) u(2)) 
    then obtain x where x: "u = Var x"
      using s(3) admissible_transactions_no_Value_consts(1)[OF T_adm u(1)] by (cases u) force+
    hence **: "x \<in> vars_transaction T"
      by (metis u(1) var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t)

    have "\<Gamma>\<^sub>v x = TAtom Value"
      using * x s(3) wt_subst_trm''[OF wt_\<sigma>\<alpha>\<I>, of u]
      by simp
    thus "t \<in> (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` fv_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
      using admissible_transaction_Value_vars_are_fv[OF T_adm **] x *
      by (metis subst_comp_set_image rev_image_eqI subst_apply_term.simps(1))
  qed
  hence 3: "vals T' \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0' \<subseteq> ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` fv_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    by (simp add: abs_apply_terms_def image_mono)

  have "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set (\<alpha>\<^sub>i\<^sub>k \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>)"
    when "t \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>" for t
    using that abs_in[OF imageI[OF that]]
          \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_ik[OF \<A>_reach T \<I> \<xi> \<sigma> \<alpha> P(1)]
          timpl_closure_set_mono[of "{t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0}" "\<alpha>\<^sub>i\<^sub>k \<A> \<I>" "\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>"
                                    "\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>"]
    unfolding a0_def a0'_def T'_def abs_intruder_knowledge_def by fast
  hence A: "\<alpha>\<^sub>i\<^sub>k (\<A>@T') \<I> \<subseteq>
              timpl_closure_set (\<alpha>\<^sub>i\<^sub>k \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>) \<union>
              (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    using 0(1) 1 by (auto simp add: abs_apply_terms_def)

  have "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set {t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0} (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>)"
    when t: "t \<in> vals_sym \<A>" for t
  proof -
    have "(\<exists>n. t = Fun (Val n) [] \<and> t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)) \<or>
          (\<exists>n. t = Var (TAtom Value,n) \<and> (TAtom Value,n) \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)"
      (is "?P \<or> ?Q")
      using t var_subterm_trms\<^sub>s\<^sub>s\<^sub>t_is_vars\<^sub>s\<^sub>s\<^sub>t[of _ "unlabel \<A>"]
            \<Gamma>\<^sub>v_TAtom[of Value] reachable_constraints_Value_vars_are_fv[OF \<A>_reach P(1)]
      unfolding vals_sym_def by fast
    thus ?thesis
    proof
      assume ?P
      then obtain n where n: "t = Fun (Val n) []" "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>)" by moura
      thus ?thesis 
        using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Val[OF \<A>_reach T \<I> \<xi> \<sigma> \<alpha> P(1), of n]
        unfolding a0_def a0'_def T'_def by fastforce
    next
      assume ?Q
      thus ?thesis
        using \<alpha>\<^sub>t\<^sub>i_covers_\<alpha>\<^sub>0_Var[OF \<A>_reach T \<I> \<xi> \<sigma> \<alpha> P(1)]
        unfolding a0_def a0'_def T'_def by fastforce
    qed
  qed
  moreover have "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0 \<in> \<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>"
    when "t \<in> vals_sym \<A>" for t
    using that abs_in vals_sym_vals
    unfolding a0_def abs_value_constants_def vals_sym_def vals_def
    by (metis (mono_tags, lifting))
  ultimately have "t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>)"
    when t: "t \<in> vals_sym \<A>" for t
    using t timpl_closure_set_mono[of "{t \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0}" "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>" "\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>"
                                      "\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>"]
    by blast
  hence "t \<cdot>\<^sub>\<alpha> a0' \<in> timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>)"
    when t: "t \<in> vals \<A>" for t
    using vals_vals_sym[OF t] by blast
  hence B: "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s (\<A>@T') \<I> \<subseteq>
              timpl_closure_set (\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I>) (\<alpha>\<^sub>t\<^sub>i \<A> T (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) \<I>) \<union>
              ((\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) ` fv_transaction T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a0'"
    using 0(2) 3
    by (simp add: abs_apply_terms_def image_subset_iff)

  have 4: "fv (t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<cdot>\<^sub>\<alpha> a) = {}" for t a
    using \<I>_grounds[of "t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] abs_fv[of "t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I>" a]
    by argo

  have "is_Fun (t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<cdot> \<I> \<cdot>\<^sub>\<alpha> a0')" for t
    using 4[of t a0'] by force
  thus ?A
    using A step_props(1,3)
    unfolding T'_def a0_def a0'_def abs_apply_terms_def
    by blast

  show ?B
    using B step_props(2,4) admissible_transaction_Value_vars[OF bspec[OF P T]]
    by (auto simp add: T'_def a0_def a0'_def abs_apply_terms_def)
qed

lemma reachable_constraints_covered:
  assumes \<A>_reach: "\<A> \<in> reachable_constraints P"
    and \<I>: "welltyped_constraint_model \<I> \<A>"
    and FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "ground (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and transactions_covered: "list_all (transaction_check (FP, OCC, TI)) P"
  shows "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
    and "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
using \<A>_reach \<I>
proof (induction rule: reachable_constraints.induct)
  case init
  { case 1 show ?case by (simp add: abs_intruder_knowledge_def) }
  { case 2 show ?case by (simp add: abs_value_constants_def) }
next
  case (step \<A> T \<xi> \<sigma> \<alpha>)
  { case 1
    hence "welltyped_constraint_model \<I> \<A>"
      by (metis welltyped_constraint_model_prefix)
    hence IH: "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
              "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
      using step.IH by metis+
    show ?case
      using reachable_constraints_covered_step[
              OF step.hyps(1,2) "1.prems" step.hyps(3-5) FP(1,2) IH(1)
                 FP(3) OCC IH(2) TI P transactions_covered]
      by metis
  }
  { case 2
    hence "welltyped_constraint_model \<I> \<A>"
      by (metis welltyped_constraint_model_prefix)
    hence IH: "\<forall>t \<in> \<alpha>\<^sub>i\<^sub>k \<A> \<I>. timpl_closure_set (set FP) (set TI) \<turnstile>\<^sub>c t"
              "\<alpha>\<^sub>v\<^sub>a\<^sub>l\<^sub>s \<A> \<I> \<subseteq> absc ` set OCC"
      using step.IH by metis+
    show ?case
      using reachable_constraints_covered_step[
              OF step.hyps(1,2) "2.prems" step.hyps(3-5) FP(1,2) IH(1)
                 FP(3) OCC IH(2) TI P transactions_covered]
      by metis
  }
qed

lemma attack_in_fixpoint_if_attack_in_ik:
  fixes FP::"('fun,'atom,'sets,'lbl) prot_terms"
  assumes "\<forall>t \<in> IK \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a. FP \<turnstile>\<^sub>c t"
    and "attack\<langle>n\<rangle> \<in> IK"
  shows "attack\<langle>n\<rangle> \<in> FP"
proof -
  have "attack\<langle>n\<rangle> \<cdot>\<^sub>\<alpha> a \<in> IK \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a" by (rule abs_in[OF assms(2)])
  hence "FP \<turnstile>\<^sub>c attack\<langle>n\<rangle> \<cdot>\<^sub>\<alpha> a" using assms(1) by blast
  moreover have "attack\<langle>n\<rangle> \<cdot>\<^sub>\<alpha> a = attack\<langle>n\<rangle>" by simp
  ultimately have "FP \<turnstile>\<^sub>c attack\<langle>n\<rangle>" by metis
  thus ?thesis using ideduct_synth_priv_const_in_ik[of FP "Attack n"] by simp
qed

lemma attack_in_fixpoint_if_attack_in_timpl_closure_set:
  fixes FP::"('fun,'atom,'sets,'lbl) prot_terms"
  assumes "attack\<langle>n\<rangle> \<in> timpl_closure_set FP TI"
  shows "attack\<langle>n\<rangle> \<in> FP"
proof -
  have "\<forall>f \<in> funs_term (attack\<langle>n\<rangle>). \<not>is_Abs f" by auto
  thus ?thesis using timpl_closure_set_no_Abs_in_set[OF assms] by blast
qed

theorem prot_secure_if_fixpoint_covered_typed:
  assumes FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "ground (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
    and transactions_covered: "list_all (transaction_check (FP, OCC, TI)) P"
    and attack_notin_FP: "attack\<langle>n\<rangle> \<notin> set FP"
    and \<A>: "\<A> \<in> reachable_constraints P"
  shows "\<nexists>\<I>. welltyped_constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])" (is "\<nexists>\<I>. ?P \<I>")
proof
  assume "\<exists>\<I>. ?P \<I>"
  then obtain \<I> where \<I>: "welltyped_constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
    by moura

  have 0: "attack\<langle>n\<rangle> \<notin> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>"
    using welltyped_constraint_model_prefix[OF \<I>]
          reachable_constraints_covered(1)[OF \<A> _ FP OCC TI P transactions_covered]
          attack_in_fixpoint_if_attack_in_ik[
            of "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>" "\<alpha>\<^sub>0 (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>)" "timpl_closure_set (set FP) (set TI)" n]
          attack_in_fixpoint_if_attack_in_timpl_closure_set
          attack_notin_FP
    unfolding abs_intruder_knowledge_def by blast

  have 1: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> attack\<langle>n\<rangle>"
    using \<I> strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" _ \<I>]
    unfolding welltyped_constraint_model_def constraint_model_def by force

  show False
    using 0 private_const_deduct[OF _ 1]
          reachable_constraints_receive_attack_if_attack'(1)[
            OF \<A> P welltyped_constraint_model_prefix[OF \<I>] 1]
    by simp
qed

end


subsection \<open>Theorem: A Protocol is Secure if it is Covered by a Fixed-Point\<close>
context stateful_protocol_model
begin

theorem prot_secure_if_fixpoint_covered:
  fixes P
  assumes FP:
      "analyzed (timpl_closure_set (set FP) (set TI))"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
      "ground (set FP)"
    and OCC:
      "\<forall>t \<in> timpl_closure_set (set FP) (set TI). \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
      "timpl_closure_set (absc ` set OCC) (set TI) \<subseteq> absc ` set OCC"
    and TI:
      "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and M:
      "has_all_wt_instances_of \<Gamma> (\<Union>T \<in> set P. trms_transaction T) N"
      "finite N"
      "tfr\<^sub>s\<^sub>e\<^sub>t N"
      "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and P:
      "\<forall>T \<in> set P. admissible_transaction T"
      "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    and transactions_covered: "list_all (transaction_check (FP, OCC, TI)) P"
    and attack_notin_FP: "attack\<langle>n\<rangle> \<notin> set FP"
    and A: "\<A> \<in> reachable_constraints P"
  shows "\<nexists>\<I>. constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
    (is "\<nexists>\<I>. constraint_model \<I> ?A")
proof
  assume "\<exists>\<I>. constraint_model \<I> ?A"
  then obtain \<I> where "constraint_model \<I> ?A" by moura
  then obtain \<I>\<^sub>\<tau> where I: "welltyped_constraint_model \<I>\<^sub>\<tau> ?A"
    using reachable_constraints_typing_result[OF M P A] by blast

  note a = FP OCC TI P(1) transactions_covered attack_notin_FP A

  show False
    using prot_secure_if_fixpoint_covered_typed[OF a] I
    by force
qed

end

subsection \<open>Alternative Protocol-Coverage Check\<close>
context stateful_protocol_model
begin

context
begin

private lemma transaction_check_variant_soundness_aux0:
  assumes S: "S \<equiv> unlabel (transaction_strand T)"
    and xs: "xs \<equiv> filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) (fv_list\<^sub>s\<^sub>s\<^sub>t S)"
    and x: "fst x = Var Value" "x \<in> fv_transaction T" "x \<notin> set (transaction_fresh T)"
  shows "x \<in> set xs"
using x fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
unfolding xs S by auto

private lemma transaction_check_variant_soundness_aux1:
  fixes T FP S C xs OCC negs poss as
  assumes C: "C \<equiv> unlabel (transaction_checks T)"
    and S: "S \<equiv> unlabel (transaction_strand T)"
    and xs: "xs \<equiv> filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) (fv_list\<^sub>s\<^sub>s\<^sub>t S)"
    and poss: "poss \<equiv> transaction_poschecks_comp C"
    and negs: "negs \<equiv> transaction_negchecks_comp C"
    and as: "as \<equiv> map (\<lambda>x. (x, set (filter (\<lambda>ab. poss x \<subseteq> ab \<and> negs x \<inter> ab = {}) OCC))) xs"
    and f: "f \<equiv> \<lambda>x. case List.find (\<lambda>p. fst p = x) as of Some p \<Rightarrow> snd p | None \<Rightarrow> {}"
    and x: "x \<in> set xs"
  shows "f x = set (filter (\<lambda>ab. poss x \<subseteq> ab \<and> negs x \<inter> ab = {}) OCC)"
proof -
  define g where "g \<equiv> \<lambda>x. set (filter (\<lambda>ab. poss x \<subseteq> ab \<and> negs x \<inter> ab = {}) OCC)"
  define gs where "gs \<equiv> map (\<lambda>x. (x, g x)) xs"

  have 1: "(x, g x) \<in> set gs" using x unfolding gs_def by simp
  
  have 2: "distinct xs" unfolding xs fv_list\<^sub>s\<^sub>s\<^sub>t_def by auto
  
  have "\<exists>i < length xs. xs ! i = x \<and> (\<forall>j < i. xs ! j \<noteq> x)" when x: "x \<in> set xs" for x
  proof (rule ex1E[OF distinct_Ex1[OF 2 x]])
    fix i assume i: "i < length xs \<and> xs ! i = x" and "\<forall>j. j < length xs \<and> xs ! j = x \<longrightarrow> j = i"
    hence "\<forall>j < length xs. xs ! j = x \<longrightarrow> j = i" by blast
    hence "\<forall>j < i. xs ! j = x \<longrightarrow> j = i" using i by auto
    hence "\<forall>j < i. xs ! j \<noteq> x" by blast 
    thus ?thesis using i by blast
  qed
  hence "\<exists>i < length gs. gs ! i = (x, g x) \<and> (\<forall>j < i. gs ! j \<noteq> (x, g x))"
    using 1 unfolding gs_def by fastforce
  hence "\<exists>i < length gs. fst (gs ! i) = x \<and> (x, g x) = gs ! i \<and> (\<forall>j < i. fst (gs ! j) \<noteq> x)"
    using nth_map[of _ xs "\<lambda>x. (x, g x)"] length_map[of "\<lambda>x. (x, g x)" xs]
    unfolding gs_def by (metis (no_types, lifting) fstI min.strict_order_iff min_less_iff_conj)
  hence "List.find (\<lambda>p. fst p = x) gs = Some (x, g x)"
    using find_Some_iff[of "\<lambda>p. fst p = x" gs "(x, g x)"] by blast
  thus ?thesis
    unfolding f as gs_def g_def by force
qed

private lemma transaction_check_variant_soundness_aux2:
  fixes T FP S C xs OCC negs poss as
  assumes C: "C \<equiv> unlabel (transaction_checks T)"
    and S: "S \<equiv> unlabel (transaction_strand T)"
    and xs: "xs \<equiv> filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) (fv_list\<^sub>s\<^sub>s\<^sub>t S)"
    and poss: "poss \<equiv> transaction_poschecks_comp C"
    and negs: "negs \<equiv> transaction_negchecks_comp C"
    and as: "as \<equiv> map (\<lambda>x. (x, set (filter (\<lambda>ab. poss x \<subseteq> ab \<and> negs x \<inter> ab = {}) OCC))) xs"
    and f: "f \<equiv> \<lambda>x. case List.find (\<lambda>p. fst p = x) as of Some p \<Rightarrow> snd p | None \<Rightarrow> {}"
    and x: "x \<notin> set xs"
  shows "f x = {}"
proof -
  define g where "g \<equiv> \<lambda>x. set (filter (\<lambda>ab. poss x \<subseteq> ab \<and> negs x \<inter> ab = {}) OCC)"
  define gs where "gs \<equiv> map (\<lambda>x. (x, g x)) xs"

  have "(x, y) \<notin> set gs" for y using x unfolding gs_def by force
  thus ?thesis
    using find_None_iff[of "\<lambda>p. fst p = x" gs]
    unfolding f as gs_def g_def by fastforce
qed

private lemma synth_abs_substs_constrs_rel_if_synth_abs_substs_constrs:
  fixes T OCC negs poss
  defines "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
    and "ts \<equiv> trms_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_receive T))"
  assumes ts_wf: "\<forall>t \<in> set ts. wf\<^sub>t\<^sub>r\<^sub>m t"
    and FP_ground: "ground (set FP)"
    and FP_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
  shows "synth_abs_substs_constrs_rel FP OCC TI ts (synth_abs_substs_constrs (FP,OCC,TI) T)"
proof -
  let ?R = "synth_abs_substs_constrs_rel FP OCC TI"
  let ?D = "synth_abs_substs_constrs_aux FP OCC TI"

  have *: "?R [t] (?D t)" when "wf\<^sub>t\<^sub>r\<^sub>m t" for t using that
  proof (induction t)
    case (Var x) thus ?case
      using synth_abs_substs_constrs_rel.SolveValueVar[of "?D (Var x)" OCC x TI FP]
      by fastforce
  next
    case (Fun f ss)
    let ?xs = "fv (Fun f ss)"
    let ?lst = "map (match_abss OCC TI (Fun f ss)) FP"

    define flt where
      "flt = (\<lambda>\<delta>::(('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set set) option. \<delta> \<noteq> None)"
    define \<Delta> where "\<Delta> = map the (filter flt (map (match_abss OCC TI (Fun f ss)) FP))"
    define \<Theta> where "\<Theta> = (\<lambda>\<delta>::('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set set. \<lambda>x.
      if \<delta> x \<noteq> {} then \<delta> x else set OCC)"
    define \<theta>1 where "\<theta>1 = fun_point_Union (\<Theta> ` set \<Delta>)"
    define \<theta>2 where "\<theta>2 = fun_point_Inter (?D ` set ss)"

    have f: "arity f = length ss" using wf_trm_arity[OF Fun.prems] by simp 

    have IH: "?R [s] (?D s)" when s: "s \<in> set ss" for s
      using Fun.IH[OF s wf_trm_subterm[OF Fun.prems Fun_param_is_subterm[OF s]]] s
      by force

    have \<Delta>3: "\<forall>\<delta>. \<delta> \<in> set \<Delta> \<longleftrightarrow> (\<exists>s \<in> set FP. match_abss OCC TI (Fun f ss) s = Some \<delta>)"
        (is "\<forall>\<delta>. \<delta> \<in> set \<Delta> \<longleftrightarrow> ?P \<delta>")
    proof (intro allI iffI)
      fix \<delta> assume "\<delta> \<in> set \<Delta>"
      then obtain u where "u \<in> set FP" "match_abss OCC TI (Fun f ss) u = Some \<delta>"
        unfolding \<Delta>_def flt_def by fastforce
      thus "?P \<delta>" by blast
    next
      fix \<delta> assume "?P \<delta>"
      then obtain u where u: "u \<in> set FP" "match_abss OCC TI (Fun f ss) u = Some \<delta>" by blast

      have "Some \<delta> \<in> set ?lst" using u unfolding flt_def by force
      hence "Some \<delta> \<in> set (filter flt ?lst)" unfolding flt_def by force
      moreover have "\<exists>\<theta>. d = Some \<theta>" when d: "d \<in> set (filter flt ?lst)" for d
        using d unfolding flt_def by simp
      ultimately have "\<delta> \<in> set (map the (filter flt ?lst))" by force
      thus "\<delta> \<in> set \<Delta>" unfolding \<Delta>_def by blast
    qed

    show ?case
    proof (cases "ss = []")
      case True
      note ss = this
      show ?thesis
      proof (cases "\<not>public f \<and> Fun f ss \<notin> set FP")
        case True thus ?thesis
          using synth_abs_substs_constrs_rel.SolvePrivConstNotin[of f FP OCC TI]
          unfolding ss by force
      next
        case False thus ?thesis
          using f synth_abs_substs_constrs_rel.SolvePubConst[of f FP OCC TI]
                synth_abs_substs_constrs_rel.SolvePrivConstIn[of f FP OCC TI]
          unfolding ss by auto
      qed
    next
      case False
      note ss = this
      hence f': "arity f > 0" using f by auto
      have IH': "?R ss (fun_point_Inter (?D ` set ss))"
        using IH synth_abs_substs_constrs_rel.SolveCons[OF ss, of FP OCC TI ?D] by blast

      have "?D (Fun f ss) = (
              fun_point_union (fun_point_Union_list (map \<Theta> \<Delta>)) (fun_point_Inter_list (map ?D ss)))"
        using ss synth_abs_substs_constrs_aux.simps(2)[of FP OCC TI f ss]
        unfolding Let_def \<Delta>_def flt_def \<Theta>_def by argo
      hence "?D (Fun f ss) = fun_point_union \<theta>1 \<theta>2"
        using fun_point_Inter_set_eq[of "map ?D ss"] fun_point_Union_set_eq[of "map \<Theta> \<Delta>"]
        unfolding \<theta>1_def \<theta>2_def by simp
      thus ?thesis
        using synth_abs_substs_constrs_rel.SolveComposed[
                OF f' f[symmetric] \<Delta>3 \<Theta>_def \<theta>1_def IH']
        unfolding \<theta>2_def by argo
    qed
  qed

  note l0 = synth_abs_substs_constrs_rel.SolveNil[of FP OCC TI]
  note d0 = synth_abs_substs_constrs_def ts_def

  note l1 = * ts_wf synth_abs_substs_constrs_rel.SolveCons[of ts FP OCC TI ?D]
  note d1 = d0 Let_def fun_point_Inter_set_eq[symmetric] fun_point_Inter_def

  show ?thesis
  proof (cases "ts = []")
    case True thus ?thesis using l0 unfolding d0 by simp
  next
    case False thus ?thesis using l1 unfolding d1 by auto
  qed
qed

private function (sequential) match_abss'_timpls_transform
::"('c set \<times> 'c set) list \<Rightarrow>
   ('a,'b,'c,'d) prot_subst \<Rightarrow>
   ('a,'b,'c,'d) prot_term \<Rightarrow>
   ('a,'b,'c,'d) prot_term \<Rightarrow>
   (('a,'b,'c,'d) prot_var \<Rightarrow> 'c set set) option"
where
  "match_abss'_timpls_transform TI \<delta> (Var x) (Fun (Abs a) _) = (
    if \<exists>b ts. \<delta> x = Fun (Abs b) ts \<and> (a = b \<or> (a,b) \<in> set TI)
    then Some ((\<lambda>_. {})(x := {a}))
    else None)"
| "match_abss'_timpls_transform TI \<delta> (Fun f ts) (Fun g ss) = (
    if f = g \<and> length ts = length ss
    then map_option fun_point_Union_list (those (map2 (match_abss'_timpls_transform TI \<delta>) ts ss))
    else None)"
| "match_abss'_timpls_transform _ _ _ _ = None"
by pat_completeness auto
termination
proof -
  let ?m = "measures [size \<circ> fst \<circ> snd \<circ> snd]"

  have 0: "wf ?m" by simp

  show ?thesis
    apply (standard, use 0 in fast)
    by (metis (no_types) comp_def fst_conv snd_conv measures_less Fun_zip_size_lt(1))
qed

private lemma match_abss'_timpls_transform_Var_inv:
  assumes "match_abss'_timpls_transform TI \<delta> (Var x) (Fun (Abs a) ts) = Some \<sigma>"
  shows "\<exists>b ts. \<delta> x = Fun (Abs b) ts \<and> (a = b \<or> (a, b) \<in> set TI)"
   and "\<sigma> = ((\<lambda>_. {})(x := {a}))"
using assms match_abss'_timpls_transform.simps(1)[of TI \<delta> x a ts]
by (metis option.distinct(1), metis option.distinct(1) option.inject)

private lemma match_abss'_timpls_transform_Fun_inv:
  assumes "match_abss'_timpls_transform TI \<delta> (Fun f ts) (Fun g ss) = Some \<sigma>"
  shows "f = g" (is ?A)
    and "length ts = length ss" (is ?B)
    and "\<exists>\<theta>. Some \<theta> = those (map2 (match_abss'_timpls_transform TI \<delta>) ts ss) \<and> \<sigma> = fun_point_Union_list \<theta>" (is ?C)
    and "\<forall>(t,s) \<in> set (zip ts ss). \<exists>\<sigma>'. match_abss'_timpls_transform TI \<delta> t s = Some \<sigma>'" (is ?D)
proof -
  note 0 = assms match_abss'_timpls_transform.simps(2)[of TI \<delta> f ts g ss] option.distinct(1)
  show ?A by (metis 0)
  show ?B by (metis 0)
  show ?C by (metis (no_types, opaque_lifting) 0 map_option_eq_Some)
  thus ?D using map2_those_Some_case[of "match_abss'_timpls_transform TI \<delta>" ts ss] by fastforce
qed

private lemma match_abss'_timpl_transform_nonempty_is_fv:
  assumes "match_abss'_timpls_transform TI \<delta> s t = Some \<sigma>"
    and "\<sigma> x \<noteq> {}"
  shows "x \<in> fv s"
using assms
proof (induction s t arbitrary: TI \<delta> \<sigma> rule: match_abss'_timpls_transform.induct)
  case (1 TI \<delta> y a ts) show ?case
    using match_abss'_timpls_transform_Var_inv[OF "1.prems"(1)] "1.prems"(2)
    by fastforce
next
  case (2 TI \<delta> f ts g ss)
  note prems = "2.prems"
  note IH = "2.IH"

  obtain \<theta> where \<theta>:
          "Some \<theta> = those (map2 (match_abss'_timpls_transform TI \<delta>) ts ss)"
          "\<sigma> = fun_point_Union_list \<theta>"
      and fg: "f = g" "length ts = length ss"
    using match_abss'_timpls_transform_Fun_inv[OF prems(1)] by fast

  have "\<exists>\<sigma> \<in> set \<theta>. \<sigma> x \<noteq> {}"
    using fg(2) prems \<theta> unfolding fun_point_Union_list_def by auto
  then obtain t' s' \<sigma> where ts':
      "(t',s') \<in> set (zip ts ss)" "match_abss'_timpls_transform TI \<delta> t' s' = Some \<sigma>" "\<sigma> x \<noteq> {}"
    using those_map2_SomeD[OF \<theta>(1)[symmetric]] by blast

  show ?case
    using ts'(3) IH[OF conjI[OF fg] ts'(1) _ ts'(2)] set_zip_leftD[OF ts'(1)] by force
qed auto

private lemma match_abss'_timpls_transformI:
  fixes s t::"('a,'b,'c,'d) prot_term"
    and \<delta>::"('a,'b,'c,'d) prot_subst"
    and \<sigma>::"('a,'b,'c,'d) prot_var \<Rightarrow> 'c set set"
  assumes TI: "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and \<delta>: "timpls_transformable_to TI t (s \<cdot> \<delta>)"
    and \<sigma>: "match_abss' s t = Some \<sigma>"
    and t: "fv t = {}"
    and s: "\<forall>f \<in> funs_term s. \<not>is_Abs f"
           "\<forall>x \<in> fv s. \<exists>a. \<delta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s"
         shows "match_abss'_timpls_transform TI \<delta> s t = Some \<sigma>"
  using \<delta> \<sigma> t s
proof (induction t arbitrary: s \<delta> \<sigma>)
  case (Fun f ts)
  note prems = Fun.prems
  note IH = Fun.IH
  show ?case
  proof (cases s)
    case (Var x)
    obtain a b where a: "f = Abs a" "\<sigma> = (\<lambda>_. {})(x := {a})" and b: "\<delta> x = \<langle>b\<rangle>\<^sub>a\<^sub>b\<^sub>s"
      using match_abss'_Var_inv[OF prems(2)[unfolded Var]] prems(5)[unfolded Var]
      by auto
    thus ?thesis
      using prems(1) timpls_transformable_to_inv(3)[of TI f ts "Abs b" "[]"]
      unfolding Var by auto
  next
    case (Fun g ss)
    note 0 = timpls_transformable_to_inv[OF prems(1)[unfolded Fun subst_apply_term.simps(2)]]
    note 1 = match_abss'_Fun_inv[OF prems(2)[unfolded Fun]]

    obtain \<theta> where \<theta>: "those (map2 match_abss' ss ts) = Some \<theta>" "\<sigma> = fun_point_Union_list \<theta>"
      using 1(3) by force

    have "timpls_transformable_to TI t' (s' \<cdot> \<delta>)" "\<exists>\<sigma>'. match_abss' s' t' = Some \<sigma>'"
      when "(t',s') \<in> set (zip ts ss)" for s' t'
      by (metis 0(2) nth_map[of _ ss] zip_arg_index[OF that],
          use that 1(4) in_set_zip_swap[of t' s' ts ss] in fast)
    hence IH': "match_abss'_timpls_transform TI \<delta> s' t' = Some \<sigma>'"
      when "(t',s') \<in> set (zip ts ss)" "match_abss' s' t' = Some \<sigma>'" for s' t' \<sigma>'
      using that IH[of t' s' \<delta> \<sigma>'] prems(3-) unfolding Fun
      by (metis (no_types, lifting) set_zip_leftD set_zip_rightD subsetI subset_empty term.set_intros(2) term.set_intros(4)) 
    
    have "those (map2 (match_abss'_timpls_transform TI \<delta>) ss ts) = Some \<theta>"
      using IH' \<theta>(1) 1(4) in_set_zip_swap[of _ _ ss ts]
            those_Some_iff[of "map2 match_abss' ss ts" \<theta>]
            those_Some_iff[of "map2 (match_abss'_timpls_transform TI \<delta>) ss ts" \<theta>]
      by auto
    thus ?thesis using \<theta>(2) 1(1,2) Fun by simp
  qed
qed simp

lemma timpls_transformable_to_match_abss'_nonempty_disj':
  fixes s t::"('a,'b,'c,'d) prot_term"
    and \<delta>::"('a,'b,'c,'d) prot_subst"
    and \<sigma>::"('a,'b,'c,'d) prot_var \<Rightarrow> 'c set set"
  assumes TI: "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and \<delta>: "timpls_transformable_to TI t (s \<cdot> \<delta>)"
    and \<sigma>: "match_abss' s t = Some \<sigma>"
    and x: "x \<in> fv s"
    and t: "fv t = {}"
    and s: "\<forall>f \<in> funs_term s. \<not>is_Abs f"
           "\<forall>x \<in> fv s. \<exists>a. \<delta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s"
    and a: "\<delta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s"
  shows "\<forall>b \<in> \<sigma> x. (b,a) \<in> (set TI)\<^sup>*" (is "?P \<sigma> x")
proof -
  note 0 = match_abss'_subst_disj_nonempty[OF TI]

  have 1: "s \<cdot> \<delta> \<in> timpl_closure t (set TI)"
    using timpls_transformable_to_iff_in_timpl_closure[OF TI] \<delta> by blast

  have 2: "match_abss'_timpls_transform TI \<delta> s t = Some \<sigma>"
    using match_abss'_timpls_transformI[OF TI \<delta> \<sigma> t s] by simp

  show "?P \<sigma> x" using 2 TI x t s a
  proof (induction TI \<delta> s t arbitrary: \<sigma> rule: match_abss'_timpls_transform.induct)
    case (1 TI \<delta> y c ts) thus ?case
      using match_abss'_timpls_transform_Var_inv[OF "1.prems"(1)] by auto
  next
    case (2 TI \<delta> f ts g ss)
    obtain \<theta> where fg: "f = g" "length ts = length ss"
        and \<theta>: "Some \<theta> = those (map2 (match_abss'_timpls_transform TI \<delta>) ts ss)"
               "\<sigma> = fun_point_Union_list \<theta>"
               "\<forall>(t, s)\<in>set (zip ts ss). \<exists>\<sigma>'. match_abss'_timpls_transform TI \<delta> t s = Some \<sigma>'"
      using match_abss'_timpls_transform_Fun_inv[OF "2.prems"(1)] by blast

    have "(b,a) \<in> (set TI)\<^sup>*" when \<theta>': "\<theta>' \<in> set \<theta>" "b \<in> \<theta>' x" for \<theta>' b
    proof -
      obtain t' s' where t':
          "(t',s') \<in> set (zip ts ss)" "match_abss'_timpls_transform TI \<delta> t' s' = Some \<theta>'"
        using those_map2_SomeD[OF \<theta>(1)[symmetric] \<theta>'(1)] by blast

      have *: "fv s' = {}" "\<forall>f \<in> funs_term t'. \<not>is_Abs f" "\<forall>x \<in> fv t'. \<exists>a. \<delta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s"
        using "2.prems"(4-6) set_zip_leftD[OF t'(1)] set_zip_rightD[OF t'(1)]
        by (fastforce, fastforce, fastforce)

      have **: "x \<in> fv t'"
        using \<theta>'(2) match_abss'_timpl_transform_nonempty_is_fv[OF t'(2)] by blast

      show ?thesis
        using \<theta>'(2) "2.IH"[OF conjI[OF fg] t'(1) _ t'(2) "2.prems"(2) ** * "2.prems"(7)] by blast
    qed
    thus ?case using \<theta>(1) unfolding \<theta>(2) fun_point_Union_list_def by simp
  qed auto
qed

lemma timpls_transformable_to_match_abss'_nonempty_disj:
  fixes s t::"('a,'b,'c,'d) prot_term"
    and \<delta>::"('a,'b,'c,'d) prot_subst"
    and \<sigma>::"('a,'b,'c,'d) prot_var \<Rightarrow> 'c set set"
  assumes TI: "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and \<delta>: "timpls_transformable_to TI t (s \<cdot> \<delta>)"
    and \<sigma>: "match_abss' s t = Some \<sigma>"
    and x: "x \<in> fv s"
    and t: "fv t = {}"
    and s: "\<forall>f \<in> funs_term s. \<not>is_Abs f"
           "\<forall>x \<in> fv s. \<exists>a. \<delta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s"
  shows "\<Inter>(ticl_abs TI ` \<sigma> x) \<noteq> {}"
proof -
  have 0: "(a,b) \<in> (set TI)\<^sup>*" when y: "y \<in> fv s" "a \<in> \<sigma> y" "\<delta> y = \<langle>b\<rangle>\<^sub>a\<^sub>b\<^sub>s" for a b y
    using timpls_transformable_to_match_abss'_nonempty_disj'[OF TI \<delta> \<sigma> y(1) t s y(3)] y(2) by blast

  obtain b where b: "\<delta> x = \<langle>b\<rangle>\<^sub>a\<^sub>b\<^sub>s" using x s(2) by blast

  have "b \<in> ticl_abs TI a" when a: "a \<in> \<sigma> x" for a
    using 0[OF x a b] unfolding ticl_abs_iff[OF TI] by blast
  thus ?thesis by blast
qed

lemma timpls_transformable_to_subst_subterm:
  fixes s t::"(('a,'b,'c,'d) prot_fun, 'v) term"
    and \<delta> \<sigma>::"(('a,'b,'c,'d) prot_fun, 'v) subst"
  assumes "timpls_transformable_to TI (t \<cdot> \<delta>) (t \<cdot> \<sigma>)"
    and "s \<sqsubseteq> t"
  shows "timpls_transformable_to TI (s \<cdot> \<delta>) (s \<cdot> \<sigma>)"
using assms
proof (induction "t \<cdot> \<delta>" "t \<cdot> \<sigma>" arbitrary: t rule: timpls_transformable_to.induct)
  case (1 TI x y) thus ?case by (cases t) auto
next
  case (2 TI f T g S)
  note prems = "2.prems"
  note hyps = "2.hyps"(2-)
  note IH = "2.hyps"(1)

  show ?case
  proof (cases "s = t")
    case False
    then obtain h U u where t: "t = Fun h U" "u \<in> set U" "s \<sqsubseteq> u"
      using prems(2) by (cases t) auto
    then obtain i where i: "i < length U" "U ! i = u"
      by (metis in_set_conv_nth)

    have "timpls_transformable_to TI (u \<cdot> \<delta>) (u \<cdot> \<sigma>)"
      using t i prems(1) timpls_transformable_to_inv(2)[of TI h "U \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>" h "U \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>" i] by simp
    thus ?thesis using IH hyps t by auto
  qed (use prems in auto)
qed simp_all

lemma timpls_transformable_to_subst_match_case:
  assumes "timpls_transformable_to TI s (t \<cdot> \<theta>)"
    and "fv s = {}"
    and "\<forall>f \<in> funs_term t. \<not>is_Abs f"
    and "distinct (fv_list t)"
    and "\<forall>x \<in> fv t. \<exists>a. \<theta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s"
  shows "\<exists>\<delta>. s = t \<cdot> \<delta>"
using assms
proof (induction s "t \<cdot> \<theta>" arbitrary: t rule: timpls_transformable_to.induct)
  case (2 TI f T g S)
  note prems = "2.prems"
  note hyps = "2.hyps"(2-)
  note IH = "2.hyps"(1)

  show ?case
  proof (cases t)
    case (Var x)
    then obtain a where a: "t \<cdot> \<theta> = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s" using prems(5) by fastforce
    show ?thesis
      using hyps timpls_transformable_to_inv'[OF prems(1)[unfolded a]]
      unfolding Var by force
  next
    case (Fun h U)
    have g: "g = h" and S: "S = U \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>"
      using hyps unfolding Fun by simp_all

    note 0 = distinct_fv_list_Fun_param[OF prems(4)[unfolded Fun]]

    have 1: "\<forall>f \<in> funs_term u. \<not>is_Abs f" when u: "u \<in> set U" for u
      using prems(3) u unfolding Fun by fastforce

    have 2: "fv t' = {}" when t': "t' \<in> set T" for t'
      using t' prems(2) by simp

    have 3: "\<forall>x \<in> fv u. \<exists>a. \<theta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s" when u: "u \<in> set U" for u
      using u prems(5) unfolding Fun by simp

    have "\<not>is_Abs f"
      using prems(3) timpls_transformable_to_inv(3)[OF prems(1)[unfolded hyps[symmetric] S g]]
      unfolding Fun by auto
    hence f: "f = h" and T: "length T = length U"
      using prems(1) timpls_transformable_to_inv(1,3)[of TI f T h "U \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>"]
      unfolding Fun by fastforce+

    define \<Delta> where "\<Delta> \<equiv> \<lambda>i. if i < length T then SOME \<delta>. T ! i = U ! i \<cdot> \<delta> else undefined"

    have "timpls_transformable_to TI (T ! i) (U ! i \<cdot> \<theta>)" when i: "i < length T" for i
      using prems(1)[unfolded Fun] T i timpls_transformable_to_inv(2)[of TI f T h "U \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>" i]
      by auto
    hence "\<exists>\<delta>. T ! i = U ! i \<cdot> \<delta>" when i: "i < length T" for i
      using i T IH[OF _ _ _ 2 1 0 3, of "T ! i" "U ! i"]
      unfolding Fun g S by simp
    hence \<Delta>: "T ! i = U ! i \<cdot> \<Delta> i" when i: "i < length T" for i
      using i someI2[of "\<lambda>\<delta>. T ! i = U ! i \<cdot> \<delta>" _ "\<lambda>\<delta>. T ! i = U ! i \<cdot> \<delta>"]
      unfolding \<Delta>_def by fastforce

    define \<delta> where "\<delta> \<equiv> \<lambda>x. if \<exists>i < length T. x \<in> fv (U ! i)
                            then \<Delta> (SOME i. i < length T \<and> x \<in> fv (U ! i)) x
                            else undefined"

    have "T ! i = U ! i \<cdot> \<delta>" when i: "i < length T" for i
    proof -
      have "j = i"
        when x: "x \<in> fv (U ! i)" and j: "j < length T" "x \<in> fv (U ! j)" for j x
        using x i j T distinct_fv_list_idx_fv_disjoint[OF prems(4)[unfolded Fun], of h U]
        by (metis (no_types, lifting) disjoint_iff_not_equal neqE term.dual_order.refl)
      hence "\<delta> x = \<Delta> i x" when x: "x \<in> fv (U ! i)" for x
        using x i some_equality[of "\<lambda>i. i < length T \<and> x \<in> fv (U ! i)" i]
        unfolding \<delta>_def by (metis (no_types, lifting))
      thus ?thesis by (metis \<Delta> i term_subst_eq)
    qed
    hence "T = U \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>" by (metis (no_types, lifting) T length_map nth_equalityI nth_map)
    hence "Fun f T = Fun f U \<cdot> \<delta>" by simp
    thus ?thesis using Fun f by fast
  qed
qed simp_all

lemma timpls_transformable_to_match_abss'_case:
  assumes "timpls_transformable_to TI s (t \<cdot> \<theta>)"
    and "fv s = {}"
    and "\<forall>f \<in> funs_term t. \<not>is_Abs f"
    and "\<forall>x \<in> fv t. \<exists>a. \<theta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s"
  shows "\<exists>\<delta>. match_abss' t s = Some \<delta>"
using assms
proof (induction s "t \<cdot> \<theta>" arbitrary: t rule: timpls_transformable_to.induct)
  case (2 TI f T g S)
  note prems = "2.prems"
  note hyps = "2.hyps"(2-)
  note IH = "2.hyps"(1)

  show ?case
  proof (cases t)
    case (Var x)
    then obtain a where a: "t \<cdot> \<theta> = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s" using prems(4) by fastforce
    thus ?thesis
      using timpls_transformable_to_inv'(4)[OF prems(1)[unfolded a]] 
      by (metis (no_types) Var is_Abs_def term.sel(2) match_abss'.simps(1))
  next
    case (Fun h U)
    have g: "g = h" and S: "S = U \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>"
      using hyps unfolding Fun by simp_all

    have 1: "\<forall>f \<in> funs_term u. \<not>is_Abs f" when u: "u \<in> set U" for u
      using prems(3) u unfolding Fun by fastforce

    have 2: "fv t' = {}" when t': "t' \<in> set T" for t'
      using t' prems(2) by simp

    have 3: "\<forall>x \<in> fv u. \<exists>a. \<theta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s" when u: "u \<in> set U" for u
      using u prems(4) unfolding Fun by simp

    have "\<not>is_Abs f"
      using prems(3) timpls_transformable_to_inv(3)[OF prems(1)[unfolded hyps[symmetric] S g]]
      unfolding Fun by auto
    hence f: "f = h" and T: "length T = length U"
      using prems(1) timpls_transformable_to_inv(1,3)[of TI f T h "U \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>"]
      unfolding Fun by fastforce+

    define \<Delta> where "\<Delta> \<equiv> \<lambda>i.
      if i < length T
      then SOME \<delta>. match_abss' (U ! i) (T ! i) = Some \<delta>
      else undefined"

    have "timpls_transformable_to TI (T ! i) (U ! i \<cdot> \<theta>)" when i: "i < length T" for i
      using prems(1)[unfolded Fun] T i timpls_transformable_to_inv(2)[of TI f T h "U \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>" i]
      by auto
    hence "\<exists>\<delta>. match_abss' (U ! i) (T ! i) = Some \<delta>" when i: "i < length T" for i
      using i T IH[OF _ _ _ 2 1 3, of "T ! i" "U ! i"]
      unfolding Fun g S by simp
    hence "match_abss' (U ! i) (T ! i) = Some (\<Delta> i)" when i: "i < length T" for i
      using i someI2[of "\<lambda>\<delta>. match_abss' (U ! i) (T ! i) = Some \<delta>" _
                        "\<lambda>\<delta>. match_abss' (U ! i) (T ! i) = Some \<delta>"]
      unfolding \<Delta>_def by fastforce
    thus ?thesis
      using match_abss'_FunI[OF _ T] unfolding Fun f by auto
  qed
qed simp_all

lemma timpls_transformable_to_match_abss_case:
  assumes TI: "set TI = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and "timpls_transformable_to TI s (t \<cdot> \<theta>)"
    and "fv s = {}"
    and "\<forall>f \<in> funs_term t. \<not>is_Abs f"
    and "\<forall>x \<in> fv t. \<exists>a. \<theta> x = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s"
  shows "\<exists>\<delta>. match_abss OCC TI t s = Some \<delta>"
proof -
  obtain \<delta> where \<delta>: "match_abss' t s = Some \<delta>"
    using timpls_transformable_to_match_abss'_case[OF assms(2-)] by blast

  show ?thesis
    using \<delta> timpls_transformable_to_match_abss'_nonempty_disj[OF assms(1,2) \<delta> _ assms(3-5)]
    unfolding match_abss_def by simp
qed

private lemma transaction_check_variant_soundness_aux3:
  fixes T FP S C xs OCC negs poss as
  defines "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
    and "C \<equiv> unlabel (transaction_checks T)"
    and "S \<equiv> unlabel (transaction_strand T)"
    and "ts \<equiv> trms_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_receive T))"
    and "xs \<equiv> filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) (fv_list\<^sub>s\<^sub>s\<^sub>t S)"
  assumes TI0: "\<forall>(a,b) \<in> set TI. \<forall>(c,d) \<in> set TI. b = c \<and> a \<noteq> d \<longrightarrow> (a,d) \<in> set TI"
               "\<forall>(a,b) \<in> set TI. a \<noteq> b"
    and OCC: "\<forall>t \<in> set FP. \<forall>a. Abs a \<in> funs_term t \<longrightarrow> a \<in> set OCC"
    and FP_ground: "ground (set FP)"
    and x: "x \<in> set xs"
    and xs: "\<forall>x. x \<in> set xs \<longrightarrow> \<delta> x \<in> set OCC"
            "\<forall>x. x \<in> set xs \<longrightarrow> poss x \<subseteq> \<delta> x"
            "\<forall>x. x \<in> set xs \<longrightarrow> \<delta> x \<inter> negs x = {}"
            "\<forall>x. x \<notin> set xs \<longrightarrow> \<delta> x = {}"
    and ts: "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<delta>)"
            "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). \<forall>f \<in> funs_term t. \<not>is_Abs f"
            "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T)). fst x = TAtom Value"
    and C: "\<forall>a x s. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> set C \<longrightarrow> s \<in> \<delta> x"
           "\<forall>x s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> set C \<longrightarrow> s \<notin> \<delta> x"
    and \<sigma>: "synth_abs_substs_constrs_rel FP OCC TI ts \<sigma>"
  shows "\<delta> x \<in> \<sigma> x"
proof -
  note defs = assms(1-5)

  note TI = trancl_eqI'[OF TI0]

  have \<delta>x0: "\<delta> x \<in> set OCC" "poss x \<subseteq> \<delta> x" "\<delta> x \<inter> negs x = {}" using x xs by (blast,blast,blast)

  have ts0: "\<forall>t \<in> set ts. intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<delta>)"
    using ts(1) trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t unfolding ts_def by blast

  have ts1: "\<not>Fun (Abs n) S \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set ts" for n S
    using ts(2) funs_term_Fun_subterm'
    unfolding ts_def trms_transaction_unfold trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t[symmetric] is_Abs_def
    by fastforce

  have ts2: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set ts). fst x = TAtom Value"
    using ts(3)
    unfolding ts_def trms_transaction_unfold trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t[symmetric]
    by fastforce

  show ?thesis using \<sigma> ts0 ts1 ts2
  proof (induction rule: synth_abs_substs_constrs_rel.induct)
    case (SolvePrivConstNotin c)
    hence "intruder_synth_mod_timpls FP TI (Fun c [])" by force
    hence "list_ex (\<lambda>t. timpls_transformable_to TI t (Fun c [])) FP"
      using SolvePrivConstNotin.hyps(1,2) by simp
    then obtain t where t: "t \<in> set FP" "timpls_transformable_to TI t (Fun c [])"
      unfolding list_ex_iff by blast

    have "\<not>is_Abs c"
      using SolvePrivConstNotin.prems(2)[of _ "[]"]
      by (metis in_subterms_Union is_Abs_def list.set_intros(1))
    hence "t = Fun c []"
      using t(2) timpls_transformable_to_inv[of TI] by (cases t) auto
    thus ?case using t(1) SolvePrivConstNotin.hyps(3) by fast
  next
    case (SolveValueVar \<theta>1 y)
    have "list_ex (\<lambda>t. timpls_transformable_to TI t \<langle>\<delta> y\<rangle>\<^sub>a\<^sub>b\<^sub>s) FP"
      using SolveValueVar.prems(1-3) unfolding \<theta>_def by simp
    then obtain t where t: "t \<in> set FP" "timpls_transformable_to TI t \<langle>\<delta> y\<rangle>\<^sub>a\<^sub>b\<^sub>s"
      unfolding list_ex_iff by blast

    obtain a where a: "t = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s" "a = \<delta> y \<or> (a, \<delta> y) \<in> set TI"
    proof -
      obtain ft tst where ft: "t = Fun ft tst"
        using t(2) timpls_transformable_to_inv_Var(1)[of TI _ "\<langle>\<delta> y\<rangle>\<^sub>a\<^sub>b\<^sub>s"]
        by (cases t) auto
      
      have "tst = []" "is_Abs ft" "the_Abs ft = \<delta> y \<or> (the_Abs ft, \<delta> y) \<in> set TI"
        using timpls_transformable_to_inv'(2,4,5)[OF t(2)[unfolded ft]]
        by (simp, force, force)
      thus thesis using that[of "the_Abs ft"] ft by force 
    qed

    have "a \<in> set OCC"
      using t(1)[unfolded a(1)] OCC by auto
    thus ?case
      using \<delta>x0(1) t(1)[unfolded a(1)] a(2)
      unfolding SolveValueVar.hyps(1) ticl_abss_def ticl_abs_def
      by force
  next
    case (SolveComposed g us \<Delta> \<Theta> \<theta>1 \<theta>2) show ?case
    proof (cases "\<forall>t \<in> set us. intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<delta>)")
      case True
      hence "\<delta> x \<in> \<theta>2 x"
        using SolveComposed.IH SolveComposed.prems(2,3)
              distinct_fv_list_Fun_param[of g us] 
        by auto
      thus ?thesis unfolding fun_point_union_def by simp
    next
      case False
      hence "list_ex (\<lambda>t. timpls_transformable_to TI t (Fun g us \<cdot> \<theta> \<delta>)) FP"
        using SolveComposed.prems(1) intruder_synth_mod_timpls.simps(2)[of FP TI g "us \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta> \<delta>"]
        unfolding list_all_iff by auto
      then obtain t where t: "t \<in> set FP" "timpls_transformable_to TI t (Fun g us \<cdot> \<theta> \<delta>)"
        unfolding list_ex_iff by blast

      have t_ground: "fv t = {}"
        using t(1) FP_ground by simp

      have g_no_abs: "\<not>is_Abs f" when f: "f \<in> funs_term (Fun g us)" for f
      proof -
        obtain fts where "Fun f fts \<sqsubseteq> Fun g us" using funs_term_Fun_subterm[OF f] by blast
        thus ?thesis using SolveComposed.prems(2)[of _ fts] by (cases f) auto
      qed

      have g_\<theta>_abs: "\<exists>a. \<theta> \<delta> y = \<langle>a\<rangle>\<^sub>a\<^sub>b\<^sub>s" when y: "y \<in> fv (Fun g us)" for y
        using y SolveComposed.prems(3) unfolding \<theta>_def by fastforce
      
      obtain \<delta>' where \<delta>': "match_abss OCC TI (Fun g us) t = Some \<delta>'"
        using g_no_abs g_\<theta>_abs timpls_transformable_to_match_abss_case[OF TI t(2) t_ground ]
        by blast

      let ?h1 = "\<lambda>\<delta> x. if x \<in> fv (Fun g us) then \<delta> x else set OCC"
      let ?h2 = "\<lambda>\<delta> x. \<Inter>(ticl_abs TI ` \<delta> x)"

      obtain \<delta>'' where \<delta>'':
          "match_abss' (Fun g us) t = Some \<delta>''" "\<delta>' = ?h1 (?h2 \<delta>'')"
          "\<forall>x \<in> fv (Fun g us). \<delta>' x \<noteq> {} \<and> \<delta>' x \<noteq> {}"
        using match_abssD[OF \<delta>'] by blast

      have \<delta>'_\<Delta>: "\<delta>' \<in> \<Delta>"
        using t(1) \<delta>' SolveComposed.hyps(3) by metis

      have "\<delta> x \<in> ticl_abs TI a" when a: "a \<in> \<delta>'' x" and x_in_g: "x \<in> fv (Fun g us)" for a
      proof -
        have "fst x = TAtom Value" using x_in_g SolveComposed.prems(3) by auto
        hence "\<theta> \<delta> x = \<langle>\<delta> x\<rangle>\<^sub>a\<^sub>b\<^sub>s" unfolding \<theta>_def by simp
        hence "(a, \<delta> x) \<in> (set TI)\<^sup>*"
          using timpls_transformable_to_match_abss'_nonempty_disj'[
                  OF TI t(2) \<delta>''(1) x_in_g t_ground]
                g_no_abs g_\<theta>_abs a
          by fastforce
        thus "\<delta> x \<in> ticl_abs TI a" unfolding ticl_abs_iff[OF TI] by force
      qed
      hence "\<delta> x \<in> \<delta>' x" when x_in_g: "x \<in> fv (Fun g us)"
        using \<delta>''(2,3) x_in_g unfolding \<delta>''(1) by simp
      hence "\<delta> x \<in> \<delta>' x" when "\<delta>' x \<noteq> {}" using match_abss_OCC_if_not_fv[OF \<delta>' that] \<delta>x0(1) by blast
      hence "\<delta> x \<in> \<theta>1 x"
        using \<delta>'_\<Delta> \<delta>x0(1) unfolding SolveComposed.hyps(4,5) fun_point_Union_def by auto
      thus ?thesis unfolding fun_point_union_def by simp
    qed
  qed (auto simp add: \<delta>x0 fun_point_Inter_def)
qed

private lemma transaction_check_variant_soundness_aux4:
  fixes T FP S C xs OCC negs poss as
  defines "\<theta> \<equiv> \<lambda>\<delta> x. if fst x = TAtom Value then (absc \<circ> \<delta>) x else Var x"
    and "C \<equiv> unlabel (transaction_checks T)"
    and "S \<equiv> unlabel (transaction_strand T)"
    and "xas \<equiv> (the_Abs \<circ> the_Fun) ` set (filter (\<lambda>t. is_Fun t \<and> is_Abs (the_Fun t)) FP)"
    and "ts \<equiv> trms_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_receive T))"
    and "xs \<equiv> filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) (fv_list\<^sub>s\<^sub>s\<^sub>t S)"
    and "poss \<equiv> transaction_poschecks_comp C"
    and "negs \<equiv> transaction_negchecks_comp C"
    and "as \<equiv> map (\<lambda>x. (x, set (filter (\<lambda>ab. poss x \<subseteq> ab \<and> negs x \<inter> ab = {}) OCC))) xs"
    and "f \<equiv> \<lambda>x. case List.find (\<lambda>p. fst p = x) as of Some p \<Rightarrow> snd p | None \<Rightarrow> {}"
  assumes T_adm: "admissible_transaction T"
    and TI0: "\<forall>(a,b) \<in> set TI. \<forall>(c,d) \<in> set TI. b = c \<and> a \<noteq> d \<longrightarrow> (a,d) \<in> set TI"
             "\<forall>(a,b) \<in> set TI. a \<noteq> b"
    and OCC: "\<forall>t \<in> set FP. \<forall>a. Abs a \<in> funs_term t \<longrightarrow> a \<in> set OCC"
    and FP_ground: "ground (set FP)"
    and FP_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
    and "x \<in> set xs"
    and "\<forall>x. x \<in> set xs \<longrightarrow> \<delta> x \<in> set OCC"
    and "\<forall>x. x \<in> set xs \<longrightarrow> poss x \<subseteq> \<delta> x"
    and "\<forall>x. x \<in> set xs \<longrightarrow> \<delta> x \<inter> negs x = {}"
    and "\<forall>x. x \<notin> set xs \<longrightarrow> \<delta> x = {}"
    and "\<forall>t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_receive T). intruder_synth_mod_timpls FP TI (t \<cdot> \<theta> \<delta>)"
    and "\<forall>a x s. \<langle>a: Var x \<in> Fun (Set s) []\<rangle> \<in> set C \<longrightarrow> s \<in> \<delta> x"
    and "\<forall>x s. \<langle>Var x not in Fun (Set s) []\<rangle> \<in> set C \<longrightarrow> s \<notin> \<delta> x"
  shows "\<delta> x \<in> synth_abs_substs_constrs (FP,OCC,TI) T x"
proof -
  let ?FPT = "(FP,OCC,TI)"
  let ?P = "\<lambda>s u. let \<delta> = mgu s u
                   in \<delta> \<noteq> None \<longrightarrow> (\<forall>x \<in> fv s. is_Fun (the \<delta> x) \<longrightarrow> is_Abs (the_Fun (the \<delta> x)))"

  define \<theta>0 where "\<theta>0 \<equiv> \<lambda>x.
    if fst x = TAtom Value \<and> x \<in> fv_transaction T \<and> x \<notin> set (transaction_fresh T)
    then {ab \<in> set OCC. poss x \<subseteq> ab \<and> negs x \<inter> ab = {}} else {}"

  define g where "g \<equiv> \<lambda>x. set (filter (\<lambda>ab. poss x \<subseteq> ab \<and> negs x \<inter> ab = {}) OCC)"
  define gs where "gs \<equiv> map (\<lambda>x. (x, g x)) xs"

  note defs = assms(3-10) \<theta>0_def
  note assm = assms(11-)[unfolded defs]

  have ts0: "\<forall>t \<in> set ts. wf\<^sub>t\<^sub>r\<^sub>m t"
    using admissible_transaction_is_wellformed_transaction(4)[OF T_adm]
    unfolding admissible_transaction_terms_def wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric]
              ts_def trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t[symmetric]
              trms_transaction_unfold
    by fast

  have ts1: "\<forall>t \<in> set ts. \<forall>f \<in> funs_term t. \<not>is_Abs f"
    using protocol_transactions_no_abss[OF T_adm] funs_term_Fun_subterm
          trms\<^sub>s\<^sub>s\<^sub>t_unlabel_prefix_subset(1)
    unfolding ts_def trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t[symmetric] is_Abs_def transaction_strand_def
    by (metis (no_types, opaque_lifting) in_subterms_Union in_subterms_subset_Union subset_iff)
  
  have ts2: "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set ts). fst x = TAtom Value"
    using admissible_transaction_Value_vars[OF T_adm]
          wellformed_transaction_send_receive_fv_subset(1)[
            OF admissible_transaction_is_wellformed_transaction(1)[OF T_adm]]
    unfolding ts_def trms_transaction_unfold trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t[symmetric] \<Gamma>\<^sub>v_TAtom''(2)
    by fastforce

  have "f x = \<theta>0 x" for x
  proof (cases "fst x = Var Value \<and> x \<in> fv_transaction T \<and> x \<notin> set (transaction_fresh T)")
    case True
    hence "\<theta>0 x = {ab \<in> set OCC. poss x \<subseteq> ab \<and> negs x \<inter> ab = {}}" unfolding \<theta>0_def by argo
    thus ?thesis
      using True transaction_check_variant_soundness_aux0[OF S_def xs_def, of x]
            transaction_check_variant_soundness_aux1[
              OF C_def S_def xs_def poss_def negs_def as_def f_def, of x]
      by simp
  next
    case False
    hence 0: "\<theta>0 x = {}" unfolding \<theta>0_def by argo

    have "x \<notin> set xs"
      using False fv_list\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"]
      unfolding xs_def S_def by fastforce
    hence "List.find (\<lambda>p. fst p = x) gs = None"
      using find_None_iff[of "\<lambda>p. fst p = x" gs] unfolding gs_def by simp
    hence "f x = {}"
      unfolding f_def as_def gs_def g_def by force
    thus ?thesis using 0 by simp
  qed
  thus ?thesis
    using synth_abs_substs_constrs_rel_if_synth_abs_substs_constrs[
            OF _ FP_ground FP_wf, of T, unfolded trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t ts_def[symmetric], OF ts0]
          transaction_check_variant_soundness_aux3[
            OF TI0 OCC FP_ground assm(7-11),
            of "synth_abs_substs_constrs ?FPT T",
            unfolded trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t ts_def[symmetric],
            OF assm(12)[unfolded \<theta>_def trms_list\<^sub>s\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>s\<^sub>t ts_def[symmetric]]
               ts1 ts2 assm(13-)[unfolded C_def]]
    unfolding defs synth_abs_substs_constrs_def Let_def by blast
qed

private lemma transaction_check_variant_soundness_aux5:
  fixes FP OCC TI T S C
  defines "msgcs \<equiv> \<lambda>x a. a \<in> synth_abs_substs_constrs (FP,OCC,TI) T x"
    and "S \<equiv> unlabel (transaction_strand T)"
    and "C \<equiv> unlabel (transaction_checks T)"
    and "xs \<equiv> filter (\<lambda>x. x \<notin> set (transaction_fresh T) \<and> fst x = TAtom Value) (fv_list\<^sub>s\<^sub>s\<^sub>t S)"
    and "poss \<equiv> transaction_poschecks_comp C"
    and "negs \<equiv> transaction_negchecks_comp C"
  assumes T_adm: "admissible_transaction T"
    and TI: "\<forall>(a,b) \<in> set TI. \<forall>(c,d) \<in> set TI. b = c \<and> a \<noteq> d \<longrightarrow> (a,d) \<in> set TI"
            "\<forall>(a,b) \<in> set TI. a \<noteq> b"
    and OCC: "\<forall>t \<in> set FP. \<forall>a. Abs a \<in> funs_term t \<longrightarrow> a \<in> set OCC"
    and FP: "ground (set FP)"
            "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
    and \<delta>: "\<delta> \<in> abs_substs_fun ` set (abs_substs_set xs OCC poss negs (\<lambda>_ _. True))"
           "transaction_check_pre (FP,OCC,TI) T \<delta>"
  shows "\<delta> \<in> abs_substs_fun ` set (abs_substs_set xs OCC poss negs msgcs)"
proof -
  have 0: "\<delta> x \<in> set OCC" "poss x \<subseteq> \<delta> x" "\<delta> x \<inter> negs x = {}" when x: "x \<in> set xs" for x
    using abs_substs_abss_bounded[OF \<delta>(1) x] by simp_all

  have 1: "\<delta> x = {}" when x: "x \<notin> set xs" for x
    by (rule abs_substs_abss_bounded'[OF \<delta>(1) x])

  have 2: "msgcs x (\<delta> x)" when x: "x \<in> set xs" for x
    using 0 1 x transaction_check_variant_soundness_aux4[OF T_adm TI OCC FP, of x \<delta>]
          transaction_check_pre_ReceiveE[OF \<delta>(2)] transaction_check_pre_InSetE[OF \<delta>(2)]
          transaction_check_pre_NotInSetE[OF \<delta>(2)]
    unfolding msgcs_def xs_def C_def S_def negs_def poss_def by fast

  show ?thesis
    using abs_substs_has_abs[of xs \<delta> OCC poss negs msgcs] 0 1 2 by blast
qed

lemma transaction_check_variant_soundness:
  assumes P_adm: "\<forall>T \<in> set P. admissible_transaction T"
    and TI: "\<forall>(a,b) \<in> set TI. \<forall>(c,d) \<in> set TI. b = c \<and> a \<noteq> d \<longrightarrow> (a,d) \<in> set TI"
            "\<forall>(a,b) \<in> set TI. a \<noteq> b"
    and OCC: "\<forall>t \<in> set FP. \<forall>a. Abs a \<in> funs_term t \<longrightarrow> a \<in> set OCC"
    and FP: "ground (set FP)"
            "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
    and T_in: "T \<in> set P"
    and T_check: "transaction_check_alt1 (FP,OCC,TI) T"
  shows "transaction_check (FP,OCC,TI) T"
proof -
  have 0: "admissible_transaction T"
    using P_adm T_in by blast

  show ?thesis
    using T_check transaction_check_variant_soundness_aux5[OF 0 TI OCC FP]
    unfolding transaction_check_def transaction_check'_def transaction_check_alt1_def
              transaction_check_comp_def list_all_iff Let_def
    by force
qed

end

end


subsection \<open>Automatic Fixed-Point Computation\<close>
context stateful_protocol_model
begin

definition compute_fixpoint_fun' where
  "compute_fixpoint_fun' P (n::nat option) enable_traces \<Delta> S0 \<equiv>
    let sy = intruder_synth_mod_timpls;

        FP' = \<lambda>S. fst (fst S);
        TI' = \<lambda>S. snd (fst S);
        OCC' = \<lambda>S. remdups (
          (map (\<lambda>t. the_Abs (the_Fun (args t ! 1)))
               (filter (\<lambda>t. is_Fun t \<and> the_Fun t = OccursFact) (FP' S)))@
          (map snd (TI' S)));

        equal_states = \<lambda>S S'. set (FP' S) = set (FP' S') \<and> set (TI' S) = set (TI' S');

        trace' = \<lambda>S. snd S;

        close = \<lambda>M f. let g = remdups \<circ> f in while (\<lambda>A. set (g A) \<noteq> set A) g M;
        close' = \<lambda>M f. let g = remdups \<circ> f in while (\<lambda>A. set (g A) \<noteq> set A) g M;
        trancl_minus_refl = \<lambda>TI.
          let aux = \<lambda>ts p. map (\<lambda>q. (fst p,snd q)) (filter ((=) (snd p) \<circ> fst) ts)
          in filter (\<lambda>p. fst p \<noteq> snd p) (close' TI (\<lambda>ts. concat (map (aux ts) ts)@ts));
        snd_Ana = \<lambda>N M TI. let N' = filter (\<lambda>t. \<forall>k \<in> set (fst (Ana t)). sy M TI k) N in
          filter (\<lambda>t. \<not>sy M TI t)
                 (concat (map (\<lambda>t. filter (\<lambda>s. s \<in> set (snd (Ana t))) (args t)) N'));
        Ana_cl = \<lambda>FP TI.
          close FP (\<lambda>M. (M@snd_Ana M M TI));
        TI_cl = \<lambda>FP TI.
          close FP (\<lambda>M. (M@filter (\<lambda>t. \<not>sy M TI t)
                                  (concat (map (\<lambda>m. concat (map (\<lambda>(a,b). \<langle>a --\<guillemotright> b\<rangle>\<langle>m\<rangle>) TI)) M))));
        Ana_cl' = \<lambda>FP TI.
          let K = \<lambda>t. set (fst (Ana t));
              flt = \<lambda>M t. (\<exists>k \<in> K t. \<not>sy M TI k) \<and> (\<exists>k \<in> K t. \<exists>f \<in> funs_term k. is_Abs f);
              N = \<lambda>M. comp_timpl_closure_list (filter (flt M) M) TI
          in close FP (\<lambda>M. M@snd_Ana (N M) M TI);

        \<Delta>' = \<lambda>S. \<Delta> (FP' S, OCC' S, TI' S);
        result = \<lambda>S T \<delta>.
          let not_fresh = \<lambda>x. x \<notin> set (transaction_fresh T);
              xs = filter not_fresh (fv_list\<^sub>s\<^sub>s\<^sub>t (unlabel (transaction_strand T)));
              u = \<lambda>\<delta> x. absdbupd (unlabel (transaction_strand T)) x (\<delta> x)
          in (remdups (filter (\<lambda>t. \<not>sy (FP' S) (TI' S) t)
                              (concat (map (\<lambda>ts. the_msgs ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (absc \<circ> u \<delta>))
                                           (filter is_Send (unlabel (transaction_send T)))))),
              remdups (filter (\<lambda>s. fst s \<noteq> snd s) (map (\<lambda>x. (\<delta> x, u \<delta> x)) xs)));
        result_tuple = \<lambda>S T \<delta>. (result S T (abs_substs_fun \<delta>), if enable_traces then \<delta> else []);
        update_state = \<lambda>S. if list_ex (\<lambda>t. is_Fun t \<and> is_Attack (the_Fun t)) (FP' S) then S
          else let results = map (\<lambda>T. map (result_tuple S T) (\<Delta>' S T)) P;
                   newtrace_flt = (\<lambda>n. let x = map fst (results ! n); y = map fst x; z = map snd x
                    in set (concat y) - set (FP' S) \<noteq> {} \<or> set (concat z) - set (TI' S) \<noteq> {});
                   trace =
                    if enable_traces
                    then trace' S@[concat (map (\<lambda>i. map (\<lambda>a. (i,snd a)) (results ! i))
                                               (filter newtrace_flt [0..<length results]))]
                    else [];
                   U = map fst (concat results);
                   V = ((remdups (concat (map fst U)@FP' S),
                         remdups (filter (\<lambda>x. fst x \<noteq> snd x) (concat (map snd U)@TI' S))),
                        trace);
                   W = ((Ana_cl (TI_cl (FP' V) (TI' V)) (TI' V),
                         trancl_minus_refl (TI' V)),
                        trace' V)
          in if \<not>equal_states W S then W
          else ((Ana_cl' (FP' W) (TI' W), TI' W), trace' W);

        S = ((\<lambda>h. case n of None \<Rightarrow> while (\<lambda>S. \<not>equal_states S (h S)) h | Some m \<Rightarrow> h ^^ m)
             update_state S0)
    in ((FP' S, OCC' S, TI' S), trace' S)"

definition compute_fixpoint_fun where
  "compute_fixpoint_fun P \<equiv>
    let P' = remdups (filter (\<lambda>T. transaction_updates T \<noteq> [] \<or> transaction_send T \<noteq> []) P);
        f = transaction_check_comp (\<lambda>_ _. True)
    in fst (compute_fixpoint_fun' P' None False f (([],[]),[]))"

definition compute_fixpoint_with_trace where
  "compute_fixpoint_with_trace P \<equiv>
    compute_fixpoint_fun' P None True (transaction_check_comp (\<lambda>_ _. True)) (([],[]),[])"

definition compute_fixpoint_from_trace where
  "compute_fixpoint_from_trace P trace \<equiv>
    let \<Delta> = \<lambda>FPT T.
          let pre_check = transaction_check_pre FPT T;
              \<delta>s = map snd (filter (\<lambda>(i,as). P ! i = T) (concat trace))
          in filter (\<lambda>\<delta>. pre_check (abs_substs_fun \<delta>)) \<delta>s;
        f = compute_fixpoint_fun' \<circ> map (nth P);
        g = \<lambda>L FPT. fst ((f L (Some 1) False \<Delta> ((fst FPT,snd (snd FPT)),[])))
    in fold g (map (map fst) trace) ([],[],[])"

definition compute_reduced_attack_trace where
  "compute_reduced_attack_trace P trace \<equiv>
    let attack_in_fixpoint = list_ex (\<lambda>t. \<exists>f \<in> funs_term t. is_Attack f) \<circ> fst;
        is_attack_trace = attack_in_fixpoint \<circ> compute_fixpoint_from_trace P;
  
        trace' =
          let is_attack_transaction =
                list_ex is_Fun_Attack \<circ> concat \<circ> map the_msgs \<circ>
                filter is_Send \<circ> unlabel \<circ> transaction_send;
              trace' =
                if trace = [] then []
                else butlast trace@[filter (is_attack_transaction \<circ> nth P \<circ> fst) (last trace)]
           in trace';
    
        iter = \<lambda>trace_prev trace_rest elem (prev,rest).
          let next =
            if is_attack_trace (trace_prev@(prev@rest)#trace_rest)
            then prev
            else prev@[elem]
          in (next, tl rest);
        iter' = \<lambda>trace_part (trace_prev,trace_rest).
          let updated = foldr (iter trace_prev (tl trace_rest)) trace_part ([],tl (rev trace_part))
          in (trace_prev@[rev (fst updated)], tl trace_rest);
    
        reduced_trace = fst (fold iter' trace' ([],trace'))
    in concat reduced_trace"

end


subsection \<open>Locales for Protocols Proven Secure through Fixed-Point Coverage\<close>
type_synonym ('f,'a,'s,'l) fixpoint_triple =
  "('f,'a,'s,'l) prot_term list \<times> 's set list \<times> ('s set \<times> 's set) list"

context stateful_protocol_model
begin

definition "attack_notin_fixpoint (FPT::('fun,'atom,'sets,'lbl) fixpoint_triple) \<equiv>
  list_all (\<lambda>t. \<forall>f \<in> funs_term t. \<not>is_Attack f) (fst FPT)"

definition "protocol_covered_by_fixpoint (FPT::('fun,'atom,'sets,'lbl) fixpoint_triple) P \<equiv>
  list_all (transaction_check FPT)
           (filter (\<lambda>T. transaction_updates T \<noteq> [] \<or> transaction_send T \<noteq> []) P)"

definition "protocol_covered_by_fixpoint_alt1 (FPT::('fun,'atom,'sets,'lbl) fixpoint_triple) P \<equiv>
  list_all (transaction_check_alt1 FPT)
           (filter (\<lambda>T. transaction_updates T \<noteq> [] \<or> transaction_send T \<noteq> []) P)"

definition "analyzed_fixpoint (FPT::('fun,'atom,'sets,'lbl) fixpoint_triple) \<equiv>
  let (FP, _, TI) = FPT
  in analyzed_closed_mod_timpls FP TI"

definition "wellformed_protocol_SMP_set (P::('fun,'atom,'sets,'lbl) prot) N \<equiv>
  has_all_wt_instances_of \<Gamma> (\<Union>T \<in> set P. trms_transaction T) (set N) \<and>
  comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> (set N) \<and>
  list_all (\<lambda>T. list_all (comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<Gamma> Pair) (unlabel (transaction_strand T))) P"

definition "wellformed_protocol' (P::('fun,'atom,'sets,'lbl) prot) N \<equiv>
  list_all admissible_transaction P \<and>
  wellformed_protocol_SMP_set P N"

definition "wellformed_protocol (P::('fun,'atom,'sets,'lbl) prot) \<equiv>
  let f = \<lambda>M. remdups (concat (map subterms_list M@map (fst \<circ> Ana) M));
      N0 = remdups (concat (map (trms_list\<^sub>s\<^sub>s\<^sub>t \<circ> unlabel \<circ> transaction_strand) P));
      N = while (\<lambda>A. set (f A) \<noteq> set A) f N0
  in wellformed_protocol' P N"

definition "wellformed_fixpoint' (FPT::('fun,'atom,'sets,'lbl) fixpoint_triple) \<equiv>
  let (FP, OCC, TI) = FPT; OCC' = set OCC
  in list_all (\<lambda>t. wf\<^sub>t\<^sub>r\<^sub>m' arity t \<and> fv t = {}) FP \<and>
     list_all (\<lambda>a. a \<in> OCC') (map snd TI) \<and>
     list_all (\<lambda>t. \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> the_Abs f \<in> OCC') FP"

definition "wellformed_term_implication_graph (FPT::('fun,'atom,'sets,'lbl) fixpoint_triple) \<equiv>
  let (_, _, TI) = FPT
  in list_all (\<lambda>(a,b). list_all (\<lambda>(c,d). b = c \<and> a \<noteq> d \<longrightarrow> List.member TI (a,d)) TI) TI \<and>
     list_all (\<lambda>p. fst p \<noteq> snd p) TI"

definition "wellformed_fixpoint (FPT::('fun,'atom,'sets,'lbl) fixpoint_triple) \<equiv>
  wellformed_fixpoint' FPT \<and> wellformed_term_implication_graph FPT"

lemma wellformed_protocol_SMP_set_mono:
  assumes "wellformed_protocol_SMP_set P S"
    and "set P' \<subseteq> set P"
  shows "wellformed_protocol_SMP_set P' S"
using assms 
unfolding wellformed_protocol_SMP_set_def comp_tfr\<^sub>s\<^sub>e\<^sub>t_def has_all_wt_instances_of_def
          wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s'_def list_all_iff
by fast

lemma wellformed_protocol'_mono:
  assumes "wellformed_protocol' P S"
    and "set P' \<subseteq> set P"
  shows "wellformed_protocol' P' S"
using assms wellformed_protocol_SMP_set_mono[of P S P']
unfolding wellformed_protocol'_def list_all_iff by blast

lemma protocol_covered_by_fixpoint_if_protocol_covered_by_fixpoint_alt1:
  assumes P: "wellformed_protocol' P P_SMP"
    and FPT: "wellformed_fixpoint FPT"
    and covered: "protocol_covered_by_fixpoint_alt1 FPT P"
  shows "protocol_covered_by_fixpoint FPT P"
proof -
  obtain FP OCC TI where FPT': "FPT = (FP,OCC,TI)" by (metis surj_pair)

  note defs = FPT' wellformed_protocol'_def wellformed_fixpoint_def wellformed_fixpoint'_def
              wellformed_term_implication_graph_def Let_def
              list_all_iff wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric] wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric] 
              member_def case_prod_unfold

  have P_adm: "\<forall>T \<in> set P. admissible_transaction T"
      and TI: "\<forall>(a,b) \<in> set TI. \<forall>(c,d) \<in> set TI. b = c \<and> a \<noteq> d \<longrightarrow> (a,d) \<in> set TI"
              "\<forall>(a,b) \<in> set TI. a \<noteq> b"
      and OCC: "\<forall>t \<in> set FP. \<forall>a. Abs a \<in> funs_term t \<longrightarrow> a \<in> set OCC"
      and FP: "ground (set FP)"
              "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
    using P FPT unfolding defs by (blast, simp, simp, fastforce, simp, simp)

  show ?thesis
    using covered transaction_check_variant_soundness[OF P_adm TI OCC FP]
    unfolding protocol_covered_by_fixpoint_def protocol_covered_by_fixpoint_alt1_def
              FPT' list_all_iff
    by fastforce
qed

lemma protocol_covered_by_fixpoint_if_protocol_covered_by_fixpoint_alt1':
  assumes P: "wellformed_protocol' P P_SMP"
    and P': "set P' \<subseteq> set P"
    and FPT: "wellformed_fixpoint FPT"
    and covered: "protocol_covered_by_fixpoint_alt1 FPT P'"
  shows "protocol_covered_by_fixpoint FPT P'"
using protocol_covered_by_fixpoint_if_protocol_covered_by_fixpoint_alt1[OF _ FPT covered]
      wellformed_protocol'_mono[OF P P']
by simp

lemma protocol_covered_by_fixpoint_trivial_case:
  assumes "list_all (\<lambda>T. transaction_updates T = [] \<and> transaction_send T = []) P"
  shows "protocol_covered_by_fixpoint FPT P"
using assms
by (simp add: list_all_iff transaction_check_trivial_case protocol_covered_by_fixpoint_def)

lemma protocol_covered_by_fixpoint_empty[simp]:
  "protocol_covered_by_fixpoint FPT []"
by (simp add: protocol_covered_by_fixpoint_def)

lemma protocol_covered_by_fixpoint_Cons[simp]:
  "protocol_covered_by_fixpoint FPT (T#P) \<longleftrightarrow>
    transaction_check FPT T \<and> protocol_covered_by_fixpoint FPT P"
using transaction_check_trivial_case
unfolding protocol_covered_by_fixpoint_def case_prod_unfold by simp

lemma protocol_covered_by_fixpoint_append[simp]:
  "protocol_covered_by_fixpoint FPT (P1@P2) \<longleftrightarrow>
    protocol_covered_by_fixpoint FPT P1 \<and> protocol_covered_by_fixpoint FPT P2"
by (simp add: protocol_covered_by_fixpoint_def case_prod_unfold)

lemma protocol_covered_by_fixpoint_I1[intro]:
  assumes "list_all (protocol_covered_by_fixpoint FPT) P"
  shows "protocol_covered_by_fixpoint FPT (concat P)"
using assms by (auto simp add: protocol_covered_by_fixpoint_def list_all_iff)

lemma protocol_covered_by_fixpoint_I2[intro]:
  assumes "protocol_covered_by_fixpoint FPT P1"
    and "protocol_covered_by_fixpoint FPT P2"
  shows "protocol_covered_by_fixpoint FPT (P1@P2)"
using assms by (auto simp add: protocol_covered_by_fixpoint_def)

lemma protocol_covered_by_fixpoint_I3:
  assumes "\<forall>T \<in> set P. \<forall>\<delta>::('fun,'atom,'sets,'lbl) prot_var \<Rightarrow> 'sets set.
    transaction_check_pre FPT T \<delta> \<longrightarrow> transaction_check_post FPT T \<delta>"
  shows "protocol_covered_by_fixpoint FPT P"
using assms
unfolding protocol_covered_by_fixpoint_def transaction_check_def transaction_check'_def
          transaction_check_comp_def list_all_iff Let_def case_prod_unfold
          Product_Type.fst_conv Product_Type.snd_conv
by fastforce

lemmas protocol_covered_by_fixpoint_intros =
  protocol_covered_by_fixpoint_I1
  protocol_covered_by_fixpoint_I2
  protocol_covered_by_fixpoint_I3

lemma prot_secure_if_prot_checks:
  fixes P::"('fun,'atom,'sets,'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun,'atom,'sets,'lbl) fixpoint_triple"
  assumes attack_notin_fixpoint: "attack_notin_fixpoint FP_OCC_TI"
    and transactions_covered: "protocol_covered_by_fixpoint FP_OCC_TI P"
    and analyzed_fixpoint: "analyzed_fixpoint FP_OCC_TI"
    and wellformed_protocol: "wellformed_protocol' P N"
    and wellformed_fixpoint: "wellformed_fixpoint FP_OCC_TI"
  shows "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>. constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
proof -
  define FP where "FP \<equiv> let (FP,_,_) = FP_OCC_TI in FP"
  define OCC where "OCC \<equiv> let (_,OCC,_) = FP_OCC_TI in OCC"
  define TI where "TI \<equiv> let (_,_,TI) = FP_OCC_TI in TI"

  have attack_notin_FP: "attack\<langle>n\<rangle> \<notin> set FP"
    using attack_notin_fixpoint[unfolded attack_notin_fixpoint_def]
    unfolding list_all_iff FP_def by force

  have 1: "\<forall>(a,b) \<in> set TI. \<forall>(c,d) \<in> set TI. b = c \<and> a \<noteq> d \<longrightarrow> (a,d) \<in> set TI"
    using wellformed_fixpoint
    unfolding wellformed_fixpoint_def wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric] Let_def TI_def
              list_all_iff member_def case_prod_unfold
              wellformed_term_implication_graph_def
    by auto

  have 0: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set FP)"
    and 2: "\<forall>(a,b) \<in> set TI. a \<noteq> b"
    and 3: "snd ` set TI \<subseteq> set OCC"
    and 4: "\<forall>t \<in> set FP. \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` set OCC"
    and 5: "ground (set FP)"
    using wellformed_fixpoint
    unfolding wellformed_fixpoint_def wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric] is_Abs_def the_Abs_def
              list_all_iff Let_def case_prod_unfold set_map FP_def OCC_def TI_def
              wellformed_fixpoint'_def wellformed_term_implication_graph_def
    by (fast, fast, blast, fastforce, simp)

  have 8: "finite (set N)"
    and 9: "has_all_wt_instances_of \<Gamma> (\<Union>T \<in> set P. trms_transaction T) (set N)"
    and 10: "tfr\<^sub>s\<^sub>e\<^sub>t (set N)"
    and 11: "\<forall>T \<in> set P. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    and 12: "\<forall>T \<in> set P. admissible_transaction T"
    using wellformed_protocol[unfolded wellformed_protocol'_def wellformed_protocol_SMP_set_def]
          tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t[of "set N"]
    unfolding Let_def list_all_iff wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric] tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p[symmetric] by fast+

  have 13: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set N)"
    using wellformed_protocol[unfolded wellformed_protocol'_def wellformed_protocol_SMP_set_def]
          finite_SMP_representationD
    unfolding wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric] wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s'_def comp_tfr\<^sub>s\<^sub>e\<^sub>t_def list_all_iff
    by blast

  note TI0 = trancl_eqI'[OF 1 2]

  have "analyzed (timpl_closure_set (set FP) (set TI))"
    using analyzed_fixpoint[unfolded analyzed_fixpoint_def]
          analyzed_closed_mod_timpls_is_analyzed_timpl_closure_set[OF TI0 0]
    unfolding FP_def TI_def
    by force
  note FP0 = this 0 5

  note OCC0 = funs_term_OCC_TI_subset(1)[OF 4 3]
              timpl_closure_set_supset'[OF funs_term_OCC_TI_subset(2)[OF 4 3]]

  note M0 = 9 8 10 13

  have "list_all (transaction_check (FP, OCC, TI)) P"
    using transactions_covered[unfolded protocol_covered_by_fixpoint_def]
          transaction_check_trivial_case[of _ FP_OCC_TI]
    unfolding FP_def OCC_def TI_def list_all_iff Let_def case_prod_unfold
    by auto
  note P0 = 12 11 this attack_notin_FP

  show ?thesis by (metis prot_secure_if_fixpoint_covered[OF FP0 OCC0 TI0 M0 P0])
qed

lemma prot_secure_if_prot_checks_alt1:
  fixes P::"('fun,'atom,'sets,'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun,'atom,'sets,'lbl) fixpoint_triple"
  assumes attack_notin_fixpoint: "attack_notin_fixpoint FP_OCC_TI"
    and transactions_covered: "protocol_covered_by_fixpoint_alt1 FP_OCC_TI P"
    and analyzed_fixpoint: "analyzed_fixpoint FP_OCC_TI"
    and wellformed_protocol: "wellformed_protocol' P N"
    and wellformed_fixpoint: "wellformed_fixpoint FP_OCC_TI"
  shows "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>. constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
using prot_secure_if_prot_checks[
        OF attack_notin_fixpoint _
           analyzed_fixpoint wellformed_protocol wellformed_fixpoint]
      protocol_covered_by_fixpoint_if_protocol_covered_by_fixpoint_alt1[
        OF wellformed_protocol wellformed_fixpoint transactions_covered]
by blast

end

locale secure_stateful_protocol =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets,'lbl) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun,'atom,'sets,'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun,'atom,'sets,'lbl) fixpoint_triple"
    and P_SMP::"('fun,'atom,'sets,'lbl) prot_term list"
  assumes attack_notin_fixpoint: "pm.attack_notin_fixpoint FP_OCC_TI"
    and transactions_covered: "pm.protocol_covered_by_fixpoint FP_OCC_TI P"
    and analyzed_fixpoint: "pm.analyzed_fixpoint FP_OCC_TI"
    and wellformed_protocol: "pm.wellformed_protocol' P P_SMP"
    and wellformed_fixpoint: "pm.wellformed_fixpoint FP_OCC_TI"
begin

theorem protocol_secure:
  "\<forall>\<A> \<in> pm.reachable_constraints P. \<nexists>\<I>. pm.constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
by (rule pm.prot_secure_if_prot_checks[OF
            attack_notin_fixpoint transactions_covered
            analyzed_fixpoint wellformed_protocol wellformed_fixpoint])

corollary protocol_welltyped_secure:
  "\<forall>\<A> \<in> pm.reachable_constraints P. \<nexists>\<I>. pm.welltyped_constraint_model \<I> (\<A>@[(l, send\<langle>[attack\<langle>n\<rangle>]\<rangle>)])"
using protocol_secure unfolding pm.welltyped_constraint_model_def by fast

end

locale secure_stateful_protocol' =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets,'lbl) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun,'atom,'sets,'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun,'atom,'sets,'lbl) fixpoint_triple"
  assumes attack_notin_fixpoint': "pm.attack_notin_fixpoint FP_OCC_TI"
    and transactions_covered': "pm.protocol_covered_by_fixpoint FP_OCC_TI P"
    and analyzed_fixpoint': "pm.analyzed_fixpoint FP_OCC_TI"
    and wellformed_protocol': "pm.wellformed_protocol P"
    and wellformed_fixpoint': "pm.wellformed_fixpoint FP_OCC_TI"
begin

sublocale secure_stateful_protocol
  arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2 P
  FP_OCC_TI
  "let f = \<lambda>M. remdups (concat (map subterms_list M@map (fst \<circ> pm.Ana) M));
       N0 = remdups (concat (map (trms_list\<^sub>s\<^sub>s\<^sub>t \<circ> unlabel \<circ> transaction_strand) P))
   in while (\<lambda>A. set (f A) \<noteq> set A) f N0"
apply unfold_locales
using attack_notin_fixpoint' transactions_covered' analyzed_fixpoint'
      wellformed_protocol'[unfolded pm.wellformed_protocol_def Let_def] wellformed_fixpoint'
unfolding Let_def by blast+

end

locale secure_stateful_protocol'' =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets,'lbl) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun,'atom,'sets,'lbl) prot_transaction list"
  assumes checks: "let FPT = pm.compute_fixpoint_fun P
    in pm.attack_notin_fixpoint FPT \<and> pm.protocol_covered_by_fixpoint FPT P \<and>
       pm.analyzed_fixpoint FPT \<and> pm.wellformed_protocol P \<and> pm.wellformed_fixpoint FPT"
begin

sublocale secure_stateful_protocol'
  arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2 P "pm.compute_fixpoint_fun P"
using checks[unfolded Let_def case_prod_unfold] by unfold_locales meson+

end

locale secure_stateful_protocol''' =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets,'lbl) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun,'atom,'sets,'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun,'atom,'sets,'lbl) fixpoint_triple"
    and P_SMP::"('fun,'atom,'sets,'lbl) prot_term list"
  assumes checks': "let P' = P; FPT = FP_OCC_TI; P'_SMP = P_SMP
                    in pm.attack_notin_fixpoint FPT \<and>
                       pm.protocol_covered_by_fixpoint FPT P' \<and>
                       pm.analyzed_fixpoint FPT \<and>
                       pm.wellformed_protocol' P' P'_SMP \<and>
                       pm.wellformed_fixpoint FPT"
begin

sublocale secure_stateful_protocol
  arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2 P FP_OCC_TI P_SMP
using checks'[unfolded Let_def case_prod_unfold] by unfold_locales meson+

end

locale secure_stateful_protocol'''' =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets,'lbl) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun,'atom,'sets,'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun,'atom,'sets,'lbl) fixpoint_triple"
  assumes checks'': "let P' = P; FPT = FP_OCC_TI
                     in pm.attack_notin_fixpoint FPT \<and>
                        pm.protocol_covered_by_fixpoint FPT P' \<and>
                        pm.analyzed_fixpoint FPT \<and>
                        pm.wellformed_protocol P' \<and>
                        pm.wellformed_fixpoint FPT"
begin

sublocale secure_stateful_protocol'
  arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2 P FP_OCC_TI
using checks''[unfolded Let_def case_prod_unfold] by unfold_locales meson+

end

locale secure_stateful_protocol_alt1 =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets,'lbl) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"'lbl"
    and label_witness2::"'lbl"
  +
  fixes P::"('fun,'atom,'sets,'lbl) prot_transaction list"
    and FP_OCC_TI:: "('fun,'atom,'sets,'lbl) fixpoint_triple"
    and P_SMP::"('fun,'atom,'sets,'lbl) prot_term list"
  assumes attack_notin_fixpoint_alt1: "pm.attack_notin_fixpoint FP_OCC_TI"
    and transactions_covered_alt1: "pm.protocol_covered_by_fixpoint_alt1 FP_OCC_TI P"
    and analyzed_fixpoint_alt1: "pm.analyzed_fixpoint FP_OCC_TI"
    and wellformed_protocol_alt1: "pm.wellformed_protocol' P P_SMP"
    and wellformed_fixpoint_alt1: "pm.wellformed_fixpoint FP_OCC_TI"
begin

sublocale secure_stateful_protocol
  arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2 P
  FP_OCC_TI P_SMP
using pm.protocol_covered_by_fixpoint_if_protocol_covered_by_fixpoint_alt1[
        OF wellformed_protocol_alt1 wellformed_fixpoint_alt1 transactions_covered_alt1]
      attack_notin_fixpoint_alt1 analyzed_fixpoint_alt1
      wellformed_protocol_alt1 wellformed_fixpoint_alt1
by unfold_locales meson+

end


subsection \<open>Automatic Protocol Composition\<close>
context stateful_protocol_model
begin

definition welltyped_leakage_free_protocol where
  "welltyped_leakage_free_protocol S P \<equiv>
    let f = \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}};
        Sec = (f (set S)) - {m. {} \<turnstile>\<^sub>c m}
    in \<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau> s.
      (\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] \<A>) \<and> s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>\<^sub>\<tau> \<and>
      welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[s]\<rangle>\<rangle>])"

definition wellformed_composable_protocols where
  "wellformed_composable_protocols (P::('fun,'atom,'sets,'lbl) prot list) N \<equiv>
    let
      Ts = concat P;
      steps = remdups (concat (map transaction_strand Ts));
      MP0 = \<Union>T \<in> set Ts. trms_transaction T \<union> pair' Pair ` setops_transaction T
    in
      list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) N \<and>
      has_all_wt_instances_of \<Gamma> MP0 (set N) \<and>
      comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> (set N) \<and>
      list_all (comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<Gamma> Pair \<circ> snd) steps \<and>
      list_all wellformed_transaction Ts \<and>
      list_all admissible_transaction_terms Ts \<and>
      list_all (list_all (\<lambda>x. \<Gamma>\<^sub>v x = TAtom Value \<or> (is_Var (\<Gamma>\<^sub>v x) \<and> is_Atom (the_Var (\<Gamma>\<^sub>v x)))) \<circ>
                transaction_fresh)
               Ts \<and>
      list_all (list_all
                  (\<lambda>p. let (x,cs) = p in
                        is_Var (\<Gamma>\<^sub>v x) \<and> is_Atom (the_Var (\<Gamma>\<^sub>v x)) \<and>
                        (\<forall>c \<in> cs. \<Gamma>\<^sub>v x = \<Gamma> (Fun (Fu c) []::('fun,'atom,'sets,'lbl) prot_term))) \<circ>
                (\<lambda>T. transaction_decl T ()))
               Ts \<and>
      list_all (\<lambda>T. \<forall>x \<in> vars_transaction T. \<not>TAtom AttackType \<sqsubseteq> \<Gamma>\<^sub>v x) Ts \<and>
      list_all (\<lambda>T. \<forall>x \<in> vars_transaction T. \<forall>f \<in> funs_term (\<Gamma>\<^sub>v x). f \<noteq> Pair \<and> f \<noteq> OccursFact)
               Ts \<and>
      list_all (list_all (\<lambda>s. is_Send (snd s) \<and> length (the_msgs (snd s)) = 1 \<and>
                              is_Fun_Attack (hd (the_msgs (snd s))) \<longrightarrow>
                                the_Attack_label (the_Fun (hd (the_msgs (snd s)))) = fst s) \<circ>
                transaction_strand)
               Ts \<and>
      list_all (\<lambda>r. (\<exists>f \<in> \<Union>(funs_term ` (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd r))). f = OccursFact \<or> f = OccursSec) \<longrightarrow>
                      (is_Receive (snd r) \<or> is_Send (snd r)) \<and> fst r = \<star> \<and>
                      (\<forall>t \<in> set (the_msgs (snd r)).
                        (OccursFact \<in> funs_term t \<or> OccursSec \<in> funs_term t) \<longrightarrow>
                          is_Fun t \<and> length (args t) = 2 \<and> t = occurs (args t ! 1) \<and>
                          is_Var (args t ! 1) \<and> (\<Gamma> (args t ! 1) = TAtom Value)))
               steps"

definition composable_protocols where
  "composable_protocols (P::('fun,'atom,'sets,'lbl) prot list) Ms S \<equiv>
    let
      steps = concat (map transaction_strand (concat P));
      M_fun = (\<lambda>l. case find ((=) l \<circ> fst) Ms of Some M \<Rightarrow> set (snd M) | None \<Rightarrow> {})
    in comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> Pair steps M_fun (set S)"

lemma composable_protocols_par_comp_constr:
  fixes S f
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "Sec \<equiv> (f (set S)) - {m. intruder_synth {} m}"
  assumes Ps_pc: "wellformed_composable_protocols Ps N" "composable_protocols Ps Ms S"
  shows "\<forall>\<A> \<in> reachable_constraints (concat Ps). \<forall>\<I>. constraint_model \<I> \<A> \<longrightarrow>
            (\<exists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> \<A> \<and>
                  ((\<forall>n. welltyped_constraint_model \<I>\<^sub>\<tau> (proj n \<A>)) \<or>
                   (\<exists>\<A>' l t. prefix \<A>' \<A> \<and> suffix [(l, receive\<langle>t\<rangle>)] \<A>' \<and>
                              strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>)))"
    (is "\<forall>\<A> \<in> _. \<forall>_. _ \<longrightarrow> ?Q \<A> \<I>")
proof (intro allI ballI impI)
  fix \<A> \<I>
  assume \<A>: "\<A> \<in> reachable_constraints (concat Ps)" and \<I>: "constraint_model \<I> \<A>"

  let ?Ts = "concat Ps"
  let ?steps = "concat (map transaction_strand ?Ts)"
  let ?MP0 = "\<Union>T \<in> set ?Ts. trms_transaction T \<union> pair' Pair ` setops_transaction T"
  let ?M_fun = "\<lambda>l. case find ((=) l \<circ> fst) Ms of Some M \<Rightarrow> set (snd M) | None \<Rightarrow> {}"

  have M:
      "has_all_wt_instances_of \<Gamma> ?MP0 (set N)"
      "finite (set N)" "tfr\<^sub>s\<^sub>e\<^sub>t (set N)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set N)"
    using Ps_pc tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t[of "set N"]
    unfolding composable_protocols_def wellformed_composable_protocols_def
              Let_def list_all_iff wf\<^sub>t\<^sub>r\<^sub>m_code[symmetric]
    by fast+

  have P:
      "\<forall>T \<in> set ?Ts. wellformed_transaction T"
      "\<forall>T \<in> set ?Ts. wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
      "\<forall>T \<in> set ?Ts. list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
      "comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> Pair ?steps ?M_fun (set S)"
    using Ps_pc tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p
    unfolding wellformed_composable_protocols_def composable_protocols_def
              Let_def list_all_iff unlabel_def wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code[symmetric]
              admissible_transaction_terms_def
    by (meson, meson, fastforce, blast)

  show "?Q \<A> \<I>"
    using reachable_constraints_par_comp_constr[OF M P \<A> \<I>]
    unfolding Sec_def f_def by fast
qed

context
begin
private lemma reachable_constraints_no_leakage_alt_aux:
  fixes P lbls L
  defines "lbls \<equiv> \<lambda>T. map (the_LabelN o fst) (filter (Not o has_LabelS) (transaction_strand T))"
    and "L \<equiv> set (remdups (concat (map lbls P)))"
  assumes l: "l \<notin> L"
  shows "map (transaction_proj l) P = map transaction_star_proj P"
proof -
  have 0: "\<not>list_ex (has_LabelN l) (transaction_strand T)" when "T \<in> set P" for T
    using that l unfolding L_def lbls_def list_ex_iff by force

  have 1: "\<not>list_ex (has_LabelN l) (transaction_strand T)"
    when T: "T \<in> set (map (transaction_proj l) P)" for T
  proof -
    obtain T' where T': "T' \<in> set P" "T = transaction_proj l T'" using T by auto
    show ?thesis
      using T'(2) 0[OF T'(1)] proj_set_subset[of l "transaction_strand T'"]
            transaction_strand_proj[of l T'] 
      unfolding list_ex_iff by fastforce
  qed

  have "list_all has_LabelS (transaction_strand T)"
    when "T \<in> set (map (transaction_proj l) P)" for T
    using that 1[OF that] transaction_proj_idem[of l]
          transaction_strand_proj[of l "transaction_proj l T"]
          has_LabelS_proj_iff_not_has_LabelN[of l "transaction_strand (transaction_proj l T)"]
    by (metis (no_types) ex_map_conv)
  thus ?thesis
    using transaction_star_proj_ident_iff transaction_proj_member
          transaction_star_proj_negates_transaction_proj(1)
    by (metis (mono_tags, lifting) map_eq_conv) 
qed

private lemma reachable_constraints_star_no_leakage:
  fixes Sec P lbls k
  defines "no_leakage \<equiv> \<lambda>\<A>. \<nexists>\<I>\<^sub>\<tau> \<A>' s.
      prefix \<A>' \<A> \<and> (\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] \<A>') \<and> s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau> \<and>
      welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>'@[(k,send\<langle>[s]\<rangle>)])"
  assumes Sec: "\<forall>s \<in> Sec. \<not>{} \<turnstile>\<^sub>c s" "ground Sec"
  shows "\<forall>\<A> \<in> reachable_constraints (map transaction_star_proj P). no_leakage \<A>"
proof
  fix A assume A: "A \<in> reachable_constraints (map transaction_star_proj P)"

  have A': "\<forall>(l,a) \<in> set A. l = \<star>"
    using reachable_constraints_preserves_labels[OF A] transaction_star_proj_has_star_labels
    unfolding list_all_iff by fastforce

  show "no_leakage A"
    using constr_sem_stateful_star_proj_no_leakage[OF Sec(2) A']
          unlabel_append[of A] singleton_lst_proj(4)[of k]
    unfolding no_leakage_def welltyped_constraint_model_def constraint_model_def by fastforce
qed

private lemma reachable_constraints_no_leakage_alt:
  fixes Sec P lbls k
  defines "no_leakage \<equiv> \<lambda>\<A>. \<nexists>\<I>\<^sub>\<tau> \<A>' s.
      prefix \<A>' \<A> \<and> (\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] \<A>') \<and> s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau> \<and>
      welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>'@[(k,send\<langle>[s]\<rangle>)])"
    and "lbls \<equiv> \<lambda>T. map (the_LabelN o fst) (filter (Not o has_LabelS) (transaction_strand T))"
    and "L \<equiv> set (remdups (concat (map lbls P)))"
  assumes Sec: "\<forall>s \<in> Sec. \<not>{} \<turnstile>\<^sub>c s" "ground Sec"
    and lbl: "\<forall>l \<in> L. \<forall>\<A> \<in> reachable_constraints (map (transaction_proj l) P). no_leakage \<A>"
  shows "\<forall>l. \<forall>\<A> \<in> reachable_constraints (map (transaction_proj l) P). \<nexists>\<I>\<^sub>\<tau> \<A>'.
              interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<and>
              prefix \<A>' \<A> \<and> (\<exists>l' ts. suffix [(l', receive\<langle>ts\<rangle>)] \<A>') \<and> strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>"
proof (intro allI ballI)
  fix l \<A>
  assume \<A>: "\<A> \<in> reachable_constraints (map (transaction_proj l) P)"

  let ?Q = "\<lambda>\<I>\<^sub>\<tau> \<A>'.
    interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>) \<and>
    prefix \<A>' \<A> \<and> (\<exists>l' t. suffix [(l', receive\<langle>t\<rangle>)] \<A>') \<and> strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>"

  show "\<nexists>\<I>\<^sub>\<tau> \<A>'. ?Q \<I>\<^sub>\<tau> \<A>'"
  proof
    assume "\<exists>\<I>\<^sub>\<tau> \<A>'. ?Q \<I>\<^sub>\<tau> \<A>'"
    then obtain \<I>\<^sub>\<tau> \<A>' t n l' ts' where
        \<I>\<^sub>\<tau>: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)" and
        \<A>': "prefix \<A>' \<A>" "suffix [(l', receive\<langle>ts'\<rangle>)] \<A>'" and
        t: "t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>" and
        n: "constr_sem_stateful \<I>\<^sub>\<tau> (proj_unl n \<A>'@[send\<langle>[t]\<rangle>])"
      unfolding strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by blast
    hence 0: "welltyped_constraint_model \<I>\<^sub>\<tau> (proj n \<A>'@[(m,send\<langle>[t]\<rangle>)])" for m
      unfolding welltyped_constraint_model_def constraint_model_def by fastforce

    have t_Sec: "\<not>{} \<turnstile>\<^sub>c t" "t \<cdot> \<I>\<^sub>\<tau> = t"
      using t Sec subst_ground_ident[of t \<I>\<^sub>\<tau>] by auto

    obtain B k' s where B:
        "constr_sem_stateful \<I>\<^sub>\<tau> (proj_unl n B@[send\<langle>[t]\<rangle>])"
        "prefix (proj n B) (proj n \<A>)" "suffix [(k', receive\<langle>s\<rangle>)] (proj n B)"
        "t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj n B) \<I>\<^sub>\<tau>"
      using constr_sem_stateful_proj_priv_term_prefix_obtain[OF \<A>'(1) n t t_Sec]
      by metis
    hence 1: "welltyped_constraint_model \<I>\<^sub>\<tau> (proj n B@[(m,send\<langle>[t]\<rangle>)])" for m
      using 0 unfolding welltyped_constraint_model_def constraint_model_def by fastforce

    note 2 = reachable_constraints_transaction_proj_proj_eq
    note 3 = reachable_constraints_transaction_proj_star_proj
    note 4 = reachable_constraints_no_leakage_alt_aux

    note star_case = 0 t t_Sec(1) reachable_constraints_star_no_leakage[OF Sec]
                     \<A>'(2) 3[OF \<A>] prefix_proj(1)[OF \<A>'(1)]
                     suffix_proj(1)[OF \<A>'(2)] declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t_proj_eq

    note lbl_case = 0 t(1) \<A> \<A>' lbl 2(2)[OF \<A> \<A>'(1)]

    show False
    proof (cases "l = n")
      case True thus ?thesis
      proof (cases "l \<in> L")
        case False
        hence "map (transaction_proj l) P = map transaction_star_proj P"
          using 4 unfolding L_def lbls_def by fast
        thus ?thesis
          using lbl_case(1-4,7) star_case(4,5) True by metis
      qed (metis lbl_case no_leakage_def)
    next
      case False
      hence "no_leakage (proj n \<A>)" using star_case(4,6) unfolding no_leakage_def by fast
      thus ?thesis by (metis B(2-4) 1 no_leakage_def)
    qed
  qed
qed

private lemma reachable_constraints_no_leakage_alt'_aux1:
  fixes P::"('a,'b,'c,'d) prot_transaction list"
  defines "f \<equiv> list_all ((list_all (Not \<circ> has_LabelS)) \<circ> tl \<circ> transaction_send)"
  assumes P: "f P"
  shows "f (map (transaction_proj l) P)"
    and "f (map transaction_star_proj P)"
proof -
  let ?g = "\<lambda>T. tl (transaction_send T)"
  have "set (?g (transaction_proj l T)) \<subseteq> set (?g T)" (is "?A \<subseteq> ?C")
    and "set (?g (transaction_star_proj T)) \<subseteq> set (?g T)" (is "?B \<subseteq> ?C")
    for T::"('a,'b,'c,'d) prot_transaction"
  proof -
    obtain T1 T2 T3 T4 T5 T6 where T: "T = Transaction T1 T2 T3 T4 T5 T6" by (cases T) simp
    have "transaction_send (transaction_proj l T) = proj l (transaction_send T)"
         "transaction_send (transaction_star_proj T) = filter has_LabelS (transaction_send T)"
      using transaction_proj.simps[of l T1 T2 T3 T4 T5 T6]
            transaction_star_proj.simps[of T1 T2 T3 T4 T5 T6]
      unfolding T proj_def Let_def by auto
    hence "set (?g (transaction_proj l T)) \<subseteq> set (proj l (?g T))"
          "set (?g (transaction_star_proj T)) \<subseteq> set (filter has_LabelS (?g T))"
      unfolding proj_def
      by (metis (no_types, lifting) filter.simps(2) list.collapse list.sel(2,3)
                                    list.set_sel(2) subsetI)+
    thus "?A \<subseteq> ?C" "?B \<subseteq> ?C" using T unfolding proj_def by auto
  qed
  thus "f (map (transaction_proj l) P)" "f (map transaction_star_proj P)"
    using P unfolding f_def list_all_iff by fastforce+
qed

private lemma reachable_constraints_no_leakage_alt'_aux2:
  fixes P
  defines "f \<equiv> \<lambda>T.
    list_all is_Receive (unlabel (transaction_receive T)) \<and>
    list_all is_Check_or_Assignment (unlabel (transaction_checks T)) \<and>
    list_all is_Update (unlabel (transaction_updates T)) \<and>
    list_all is_Send (unlabel (transaction_send T))"
  assumes P: "list_all f P"
  shows "list_all f (map (transaction_proj l) P)" (is ?A)
    and "list_all f (map transaction_star_proj P)" (is ?B)
proof -
  have "f (transaction_proj l T)" (is ?A')
    and "f (transaction_star_proj T)" (is ?B')
    when T_in: "T \<in> set P" for T
  proof -
    obtain T1 T2 T3 T4 T5 T6 where T: "T = Transaction T1 T2 T3 T4 T5 T6" by (cases T)
    have "f T" using P T_in unfolding list_all_iff by simp
    thus ?A' ?B'
      unfolding f_def T unlabel_def proj_def Let_def list_all_iff
                transaction_proj.simps[of l T1 T2 T3 T4 T5 T6]
                transaction_star_proj.simps[of T1 T2 T3 T4 T5 T6]
      by auto
  qed
  thus ?A ?B unfolding list_all_iff by auto
qed

private lemma reachable_constraints_no_leakage_alt':
  fixes Sec P lbls k
  defines "no_leakage \<equiv> \<lambda>\<A>. \<nexists>\<I>\<^sub>\<tau> \<A>' s.
      prefix \<A>' \<A> \<and> (\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] \<A>') \<and> s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau> \<and>
      welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>'@[(k,send\<langle>[s]\<rangle>)])"
    and "no_leakage' \<equiv> \<lambda>\<A>. \<nexists>\<I>\<^sub>\<tau> s.
      (\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] \<A>) \<and> s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>\<^sub>\<tau> \<and>
      welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[(k,send\<langle>[s]\<rangle>)])"
  assumes P: "list_all wellformed_transaction P"
             "list_all ((list_all (Not \<circ> has_LabelS)) \<circ> tl \<circ> transaction_send) P"
    and Sec: "\<forall>s \<in> Sec. \<not>{} \<turnstile>\<^sub>c s" "ground Sec"
    and lbl: "\<forall>l \<in> L. \<forall>\<A> \<in> reachable_constraints (map (transaction_proj l) P). no_leakage' \<A>"
  shows "\<forall>l \<in> L. \<forall>\<A> \<in> reachable_constraints (map (transaction_proj l) P). no_leakage \<A>" (is ?A)
    and "\<forall>\<A> \<in> reachable_constraints (map transaction_star_proj P). no_leakage \<A>" (is ?B)
proof -
  define f where "f \<equiv> \<lambda>T::('fun,'atom,'sets,'lbl) prot_transaction.
    list_all is_Receive (unlabel (transaction_receive T)) \<and>
    list_all is_Check_or_Assignment (unlabel (transaction_checks T)) \<and>
    list_all is_Update (unlabel (transaction_updates T)) \<and>
    list_all is_Send (unlabel (transaction_send T))"

  define g where "(g::('fun,'atom,'sets,'lbl) prot_transaction \<Rightarrow> bool) \<equiv> 
    list_all (Not \<circ> has_LabelS) \<circ> tl \<circ> transaction_send"

  have P': "list_all f P"
    using P(1) unfolding wellformed_transaction_def f_def list_all_iff by fastforce

  note 0 = reachable_constraints_no_leakage_alt'_aux1[OF P(2), unfolded g_def[symmetric]]

  note 1 = reachable_constraints_no_leakage_alt'_aux2[
            OF P'[unfolded f_def], unfolded f_def[symmetric]]

  note 2 = reachable_constraints_aligned_prefix_ex[unfolded f_def[symmetric] g_def[symmetric]]

  have 3: "\<forall>\<A> \<in> reachable_constraints (map transaction_star_proj P). no_leakage' \<A>"
    using reachable_constraints_star_no_leakage[OF Sec] unfolding no_leakage'_def by blast

  show ?A
  proof (intro ballI)
    fix l \<A> assume l: "l \<in> L" and \<A>: "\<A> \<in> reachable_constraints (map (transaction_proj l) P)"
    show "no_leakage \<A>"
    proof (rule ccontr)
      assume "\<not>no_leakage \<A>"
      then obtain \<I>\<^sub>\<tau> \<A>' s where \<A>':
          "prefix \<A>' \<A>" "\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] \<A>'" "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>"
          "welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>'@[(k, send\<langle>[s]\<rangle>)])"
        unfolding no_leakage_def by blast

      have s: "\<not>{} \<turnstile>\<^sub>c s" "fv s = {}" using \<A>'(3) Sec by auto

      have \<I>\<^sub>\<tau>: "constr_sem_stateful \<I>\<^sub>\<tau> (unlabel \<A>'@[send\<langle>[s]\<rangle>])"
              "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
        using \<A>'(4) unfolding welltyped_constraint_model_def constraint_model_def by auto

      show False
        using 2[OF 1(1) 0(1) s \<A> \<A>'(1,2) \<I>\<^sub>\<tau>(1)] l lbl \<A>'(3) \<I>\<^sub>\<tau>(2,3,4)
              singleton_lst_proj(4)[of k "send\<langle>[s]\<rangle>"] unlabel_append[of _ "[(k, send\<langle>[s]\<rangle>)]"]
        unfolding no_leakage'_def welltyped_constraint_model_def constraint_model_def by metis
    qed
  qed

  show ?B
  proof (intro ballI)
    fix \<A> assume \<A>: "\<A> \<in> reachable_constraints (map transaction_star_proj P)"
    show "no_leakage \<A>"
    proof (rule ccontr)
      assume "\<not>no_leakage \<A>"
      then obtain \<I>\<^sub>\<tau> \<A>' s where \<A>':
          "prefix \<A>' \<A>" "\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] \<A>'" "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau>"
          "welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>'@[(k, send\<langle>[s]\<rangle>)])"
        unfolding no_leakage_def by blast

      have s: "\<not>{} \<turnstile>\<^sub>c s" "fv s = {}" using \<A>'(3) Sec by auto

      have \<I>\<^sub>\<tau>: "constr_sem_stateful \<I>\<^sub>\<tau> (unlabel \<A>'@[send\<langle>[s]\<rangle>])"
              "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"
        using \<A>'(4) unfolding welltyped_constraint_model_def constraint_model_def by auto

      show False
        using 2[OF 1(2) 0(2) s \<A> \<A>'(1,2) \<I>\<^sub>\<tau>(1)] 3 \<A>'(3) \<I>\<^sub>\<tau>(2,3,4)
              singleton_lst_proj(4)[of k "send\<langle>[s]\<rangle>"] unlabel_append[of _ "[(k, send\<langle>[s]\<rangle>)]"]
        unfolding no_leakage'_def welltyped_constraint_model_def constraint_model_def by metis
    qed
  qed
qed

lemma composable_protocols_par_comp_prot_alt:
  fixes S f Sec lbls Ps
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "Sec \<equiv> (f (set S)) - {m. {} \<turnstile>\<^sub>c m}"
    and "lbls \<equiv> \<lambda>T. map (the_LabelN o fst) (filter (Not o has_LabelS) (transaction_strand T))"
    and "L \<equiv> set (remdups (concat (map lbls (concat Ps))))"
    and "no_leakage \<equiv> \<lambda>\<A>. \<nexists>\<I>\<^sub>\<tau> \<A>' s.
      prefix \<A>' \<A> \<and> (\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] \<A>') \<and> s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' \<I>\<^sub>\<tau> \<and>
      welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>'@[\<langle>\<star>, send\<langle>[s]\<rangle>\<rangle>])"
  assumes Ps_pc: "wellformed_composable_protocols Ps N" "composable_protocols Ps Ms S"
    and component_secure:
          "\<forall>\<A> \<in> reachable_constraints (map (transaction_proj l) (concat Ps)). \<nexists>\<I>.
              welltyped_constraint_model \<I> (\<A>@[\<langle>l, send\<langle>[attack\<langle>ln l\<rangle>]\<rangle>\<rangle>])"
    and no_leakage:
          "\<forall>l \<in> L. \<forall>\<A> \<in> reachable_constraints (map (transaction_proj l) (concat Ps)). no_leakage \<A>"
  shows "\<forall>\<A> \<in> reachable_constraints (concat Ps). \<nexists>\<I>.
            constraint_model \<I> (\<A>@[\<langle>l, send\<langle>[attack\<langle>ln l\<rangle>]\<rangle>\<rangle>])"
proof
  fix \<A>
  assume \<A>: "\<A> \<in> reachable_constraints (concat Ps)"
  let ?att = "[\<langle>l, send\<langle>[attack\<langle>ln l\<rangle>]\<rangle>\<rangle>]"

  define Q where "Q \<equiv> \<lambda>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"

  define R where "R \<equiv> \<lambda>\<A> \<I>\<^sub>\<tau>.
    \<exists>\<A>' l t. prefix \<A>' \<A> \<and> suffix [(l, receive\<langle>t\<rangle>)] \<A>' \<and> strand_leaks\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A>' Sec \<I>\<^sub>\<tau>"

  define M where "M \<equiv> \<Union>T\<in>set (concat Ps). trms_transaction T \<union> pair' Pair ` setops_transaction T"

  have Sec: "\<forall>s \<in> Sec. \<not>{} \<turnstile>\<^sub>c s" "ground Sec" unfolding Sec_def f_def by auto

  have par_comp':
      "\<forall>\<A> \<in> reachable_constraints (concat Ps). \<forall>\<I>. constraint_model \<I> \<A> \<longrightarrow>
         (\<exists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> \<A> \<and>
              ((\<forall>n. welltyped_constraint_model \<I>\<^sub>\<tau> (proj n \<A>)) \<or> R \<A> \<I>\<^sub>\<tau>))"
    using \<A> composable_protocols_par_comp_constr[OF Ps_pc] unfolding Sec_def f_def R_def by fast

  have "\<forall>l. \<forall>\<A> \<in> reachable_constraints (map (transaction_proj l) (concat Ps)). \<nexists>\<I>\<^sub>\<tau>. Q \<I>\<^sub>\<tau> \<and> R \<A> \<I>\<^sub>\<tau>"
    using reachable_constraints_no_leakage_alt[OF
            Sec no_leakage[unfolded no_leakage_def L_def lbls_def]]
    unfolding Q_def R_def by blast
  hence no_leakage':
      "\<forall>\<A> \<in> reachable_constraints (concat Ps). \<nexists>\<I>\<^sub>\<tau>. Q \<I>\<^sub>\<tau> \<and> R \<A> \<I>\<^sub>\<tau>"
    using reachable_constraints_component_leaks_if_composed_leaks[OF Sec, of "concat Ps"
            "\<lambda>\<I>\<^sub>\<tau>. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>\<^sub>\<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>\<^sub>\<tau>)"]
    unfolding Q_def R_def by blast

  have M: "has_all_wt_instances_of \<Gamma> M (set N)" "finite (set N)" "tfr\<^sub>s\<^sub>e\<^sub>t (set N)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set N)"
   and P: "\<forall>T \<in> set (concat Ps). wellformed_transaction T"
          "\<forall>T \<in> set (concat Ps). admissible_transaction_terms T"
          "\<forall>T \<in> set (concat Ps). \<forall>x \<in> vars_transaction T. \<not>TAtom AttackType \<sqsubseteq> \<Gamma>\<^sub>v x"
          "\<forall>T \<in> set (concat Ps). \<forall>s \<in> set (transaction_strand T).
              is_Send (snd s) \<and> length (the_msgs (snd s)) = 1 \<and>
              is_Fun_Attack (hd (the_msgs (snd s))) \<longrightarrow>
                the_Attack_label (the_Fun (hd (the_msgs (snd s)))) = fst s"
          "\<forall>T \<in> set (concat Ps). list_all tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p (unlabel (transaction_strand T))"
    using Ps_pc(1) tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>s\<^sub>t\<^sub>p
    unfolding wellformed_composable_protocols_def list_all_iff Let_def M_def
              wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s'_def wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_code unlabel_def \<Gamma>\<^sub>v_TAtom''(1,2)
    by (force, force, fast, fast, fast, fast, fast, simp, simp)

  have P_fresh: "\<forall>T \<in> set (concat Ps). \<forall>x \<in> set (transaction_fresh T).
                  \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a))"
      (is "\<forall>T \<in> ?P. \<forall>x \<in> ?frsh T. ?Q x")
  proof (intro ballI)
    fix T x assume T: "T \<in> ?P" "x \<in> ?frsh T"
    hence "\<Gamma>\<^sub>v x = TAtom Value \<or> (is_Var (\<Gamma>\<^sub>v x) \<and> is_Atom (the_Var (\<Gamma>\<^sub>v x)))"
      using Ps_pc(1) unfolding wellformed_composable_protocols_def list_all_iff Let_def by fastforce
    thus "?Q x" by (metis prot_atom.is_Atom_def term.collapse(1))
  qed

  have P': "\<forall>T \<in> set (concat Ps). wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s' arity (trms_transaction T)"
    using P(2) admissible_transaction_terms_def by fast

  have "\<not>welltyped_constraint_model \<I> (\<A>@?att)" for \<I>
  proof
    assume "welltyped_constraint_model \<I> (\<A>@?att)"
    hence \<I>: "welltyped_constraint_model \<I> \<A>" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I> \<turnstile> attack\<langle>ln l\<rangle>"
      using strand_sem_append_stateful[of "{}" "{}" "unlabel \<A>" "unlabel ?att"]
            unlabel_append[of \<A> ?att]
      unfolding welltyped_constraint_model_def constraint_model_def by auto

    obtain \<I>\<^sub>\<tau> where \<I>\<^sub>\<tau>:
        "welltyped_constraint_model \<I>\<^sub>\<tau> \<A>"
        "welltyped_constraint_model \<I>\<^sub>\<tau> (proj l \<A>)"
      using \<A> \<I> no_leakage' par_comp'
      unfolding Q_def welltyped_constraint_model_def constraint_model_def by metis

    have "\<langle>l, receive\<langle>[attack\<langle>ln l\<rangle>]\<rangle>\<rangle> \<in> set \<A>"
      using reachable_constraints_receive_attack_if_attack(3)[OF \<A> P(1-2) P_fresh P(3) \<I> P(4)]
      by auto
    hence "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>\<^sub>\<tau> \<turnstile> attack\<langle>ln l\<rangle>"
      using in_proj_set[of l "receive\<langle>[attack\<langle>ln l\<rangle>]\<rangle>" \<A>] in_ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t_iff[of "attack\<langle>ln l\<rangle>" "proj l \<A>"]
            intruder_deduct.Axiom[of "attack\<langle>ln l\<rangle>" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (proj l \<A>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>\<^sub>\<tau>"]
      by fastforce
    hence "welltyped_constraint_model \<I>\<^sub>\<tau> (proj l \<A>@?att)"
      using \<I>\<^sub>\<tau> strand_sem_append_stateful[of "{}" "{}" "unlabel (proj l \<A>)" "unlabel ?att" \<I>\<^sub>\<tau>]
      unfolding welltyped_constraint_model_def constraint_model_def by auto
    thus False
      using component_secure reachable_constraints_transaction_proj[OF \<A>, of l] by simp
  qed
  thus "\<nexists>\<I>. constraint_model \<I> (\<A>@?att)"
    using reachable_constraints_typing_result'[OF M_def M P(1) P' P(5) \<A>] by blast
qed

lemma composable_protocols_par_comp_prot:
  fixes S f Sec lbls Ps
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "Sec \<equiv> (f (set S)) - {m. {} \<turnstile>\<^sub>c m}"
    and "lbls \<equiv> \<lambda>T. map (the_LabelN o fst) (filter (Not o has_LabelS) (transaction_strand T))"
    and "L \<equiv> set (remdups (concat (map lbls (concat Ps))))"
    and "no_leakage \<equiv> \<lambda>\<A>. \<nexists>\<I>\<^sub>\<tau> s.
      (\<exists>l ts. suffix [(l, receive\<langle>ts\<rangle>)] \<A>) \<and> s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<A> \<I>\<^sub>\<tau> \<and>
      welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[s]\<rangle>\<rangle>])"
  assumes Ps_pc: "wellformed_composable_protocols Ps N" "composable_protocols Ps Ms S"
                 "list_all ((list_all (Not \<circ> has_LabelS)) \<circ> tl \<circ> transaction_send) (concat Ps)"
    and component_secure:
          "\<forall>\<A> \<in> reachable_constraints (map (transaction_proj l) (concat Ps)). \<nexists>\<I>.
              welltyped_constraint_model \<I> (\<A>@[\<langle>l, send\<langle>[attack\<langle>ln l\<rangle>]\<rangle>\<rangle>])"
    and no_leakage:
          "\<forall>l \<in> L. \<forall>\<A> \<in> reachable_constraints (map (transaction_proj l) (concat Ps)). no_leakage \<A>"
  shows "\<forall>\<A> \<in> reachable_constraints (concat Ps). \<nexists>\<I>.
            constraint_model \<I> (\<A>@[\<langle>l, send\<langle>[attack\<langle>ln l\<rangle>]\<rangle>\<rangle>])"
proof -
  have P': "list_all wellformed_transaction (concat Ps)"
    using Ps_pc(1) unfolding wellformed_composable_protocols_def by meson

  have Sec: "\<forall>s \<in> Sec. \<not>{} \<turnstile>\<^sub>c s" "ground Sec" unfolding Sec_def f_def by auto

  note 0 = composable_protocols_par_comp_prot_alt[
            OF Ps_pc(1,2) component_secure, unfolded lbls_def[symmetric] L_def[symmetric]]

  note 1 = reachable_constraints_no_leakage_alt'[
            OF P' Ps_pc(3) Sec no_leakage[unfolded no_leakage_def]]

  show ?thesis using 0 1 unfolding f_def Sec_def by argo
qed

lemma composable_protocols_par_comp_prot':
  assumes P_defs:
      "Pc = concat Ps"
      "set Ps_with_stars =
        (\<lambda>n. map (transaction_proj n) Pc) `
          set (remdups (concat
                (map (\<lambda>T. map (the_LabelN \<circ> fst) (filter (Not \<circ> has_LabelS) (transaction_strand T)))
                  Pc)))"
    and Ps_wellformed:
      "list_all (list_all (Not \<circ> has_LabelS) \<circ> tl \<circ> transaction_send) Pc"
      "wellformed_composable_protocols Ps N"
      "composable_protocols Ps Ms S"
    and Ps_no_leakage:
      "list_all (welltyped_leakage_free_protocol S) Ps_with_stars"
    and P_def:
      "P = map (transaction_proj n) Pc"
    and P_wt_secure:
      "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>.
        welltyped_constraint_model \<I> (\<A>@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
  shows "\<forall>\<A> \<in> reachable_constraints Pc. \<nexists>\<I>.
          constraint_model \<I> (\<A>@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
by (rule composable_protocols_par_comp_prot[
          OF Ps_wellformed(2,3,1)[unfolded P_defs(1)]
             P_wt_secure[unfolded P_def[unfolded P_defs(1)]]
             transaction_proj_ball_subst[
               OF P_defs(2)[unfolded P_defs(1)]
                  Ps_no_leakage(1)[
                    unfolded list_all_iff welltyped_leakage_free_protocol_def Let_def]],
          unfolded P_defs(1)[symmetric]])

end

context
begin

lemma welltyped_constraint_model_leakage_model_swap:
  fixes I \<alpha> \<delta>::"('fun,'atom,'sets,'lbl) prot_subst" and s
  assumes A: "welltyped_constraint_model I (A@[\<langle>\<star>, send\<langle>[s \<cdot> \<delta>]\<rangle>\<rangle>])"
    and \<alpha>: "transaction_renaming_subst \<alpha> P A"
    and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "subst_domain \<delta> = fv s" "ground (subst_range \<delta>)"
  obtains J
    where "welltyped_constraint_model J (A@[\<langle>\<star>, send\<langle>[s \<cdot> \<delta>]\<rangle>\<rangle>])"
    and "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J \<turnstile> s \<cdot> \<alpha> \<cdot> J"
proof
  note defs = welltyped_constraint_model_def constraint_model_def
  note \<delta>_s = subst_fv_dom_ground_if_ground_img[OF equalityD2[OF \<delta>(3)] \<delta>(4)]
  note \<alpha>' = transaction_renaming_subst_is_renaming(2)[OF \<alpha>]
            inj_on_subset[OF transaction_renaming_subst_is_injective[OF \<alpha>]
                             subset_UNIV[of "fv s"]]
            transaction_renaming_subst_var_obtain(2)[OF \<alpha>, of _ s]
            transaction_renaming_subst_is_renaming(6)[OF \<alpha>, of s]
            transaction_renaming_subst_vars_disj(8)[OF \<alpha>]
            transaction_renaming_subst_wt[OF \<alpha>]

  define \<alpha>inv where "\<alpha>inv \<equiv> subst_var_inv \<alpha> (fv s)"
  define \<delta>' where "\<delta>' \<equiv> rm_vars (UNIV - fv (s \<cdot> \<alpha>)) (\<alpha>inv \<circ>\<^sub>s \<delta>)"
  define J where "J \<equiv> \<lambda>x. if x \<in> fv (s \<cdot> \<alpha>) then \<delta>' x else I x"

  have \<alpha>_invertible: "s = s \<cdot> \<alpha> \<circ>\<^sub>s \<alpha>inv"
    using \<alpha>'(1) inj_var_ran_subst_is_invertible'[of \<alpha> s] inj_on_subset[OF \<alpha>'(2)]
    unfolding \<alpha>inv_def by blast

  have \<delta>'_domain: "subst_domain \<delta>' = fv (s \<cdot> \<alpha>)"
  proof -
    have "x \<in> subst_domain (\<alpha>inv \<circ>\<^sub>s \<delta>)" when x: "x \<in> fv (s \<cdot> \<alpha>)" for x
    proof -
      obtain y where y: "y \<in> fv s" "\<alpha> y = Var x"
        using \<alpha>'(3)[OF x] by blast
  
      have "y \<in> subst_domain \<delta>" using y(1) \<delta>(3) by blast
      moreover have "(\<alpha>inv \<circ>\<^sub>s \<delta>) x = \<delta> y"
        using y \<alpha>'(3)[OF x] \<alpha>_invertible
              vars_term_subset_subst_eq[of "Var y" s "\<alpha> \<circ>\<^sub>s \<alpha>inv" Var]
        unfolding \<delta>'_def \<alpha>inv_def
        by (metis (no_types, lifting) fv_subst_subset subst_apply_term.simps(1)
                  subst_apply_term_empty subst_compose) 
      ultimately show ?thesis using \<delta>(4) by fastforce
    qed
    thus ?thesis using rm_vars_dom[of "UNIV - fv (s \<cdot> \<alpha>)" "\<alpha>inv \<circ>\<^sub>s \<delta>"] unfolding \<delta>'_def by blast
  qed

  have \<delta>'_range: "fv t = {}" when t: "t \<in> (subst_range \<delta>')" for t
  proof -
    obtain x where "x \<in> fv (s \<cdot> \<alpha>)" "\<delta>' x = t" using t \<delta>'_domain by auto
    thus ?thesis
      by (metis (no_types, lifting) \<delta>'_def subst_compose_def \<delta>(3,4) \<alpha>_invertible fv_subst_subset
            subst_fv_dom_ground_if_ground_img subst_subst_compose Diff_iff)
  qed

  have J0: "x \<in> fv (s \<cdot> \<alpha>) \<Longrightarrow> J x = \<delta>' x"
           "x \<notin> fv (s \<cdot> \<alpha>) \<Longrightarrow> J x = I x" for x
    unfolding J_def by (cases "x \<in> fv (s \<cdot> \<alpha>)") (simp_all add: subst_compose)

  have J1: "subst_range J \<subseteq> subst_range \<delta>' \<union> subst_range I"
  proof
    fix t assume "t \<in> subst_range J"
    then obtain x where x: "x \<in> subst_domain J" "J x = t" by auto
    hence "t = \<delta>' x \<Longrightarrow> x \<in> subst_domain \<delta>'" "t = I x \<Longrightarrow> x \<in> subst_domain I"
      by (metis subst_domI subst_dom_vars_in_subst)+
    thus "t \<in> subst_range \<delta>' \<union> subst_range I" using x(2) J0[of x] by auto
  qed
  
  have "x \<notin> fv (s \<cdot> \<alpha>)" when x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[\<langle>\<star>, send\<langle>[s \<cdot> \<delta>]\<rangle>\<rangle>])" for x
    using x \<delta>_s \<alpha>'(4) \<alpha>'(5) by auto
  hence "I x = J x" when x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A@[\<langle>\<star>, send\<langle>[s \<cdot> \<delta>]\<rangle>\<rangle>])" for x
    using x unfolding J_def \<delta>'_def by auto
  hence "constr_sem_stateful J (unlabel (A@[\<langle>\<star>, send\<langle>[s \<cdot> \<delta>]\<rangle>\<rangle>]))"
    using A strand_sem_model_swap[of "unlabel (A@[\<langle>\<star>, send\<langle>[s \<cdot> \<delta>]\<rangle>\<rangle>])" I J "{}" "{}"]
    unfolding defs by blast
  moreover have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t J"
    using A subst_var_inv_wt[OF \<alpha>'(6), of "fv s"]
          wt_subst_trm''[OF \<delta>(1)] subst_compose[of "subst_var_inv \<alpha> (fv s)" \<delta>]
    unfolding defs J_def \<delta>'_def \<alpha>inv_def wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by presburger
  moreover have "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t J"
  proof -
    have "fv t = {}" when t: "t \<in> (subst_range J)" for t
      using t A J1 \<delta>'_range unfolding defs by auto
    moreover have "x \<in> subst_domain J" for x
    proof (cases "x \<in> fv (s \<cdot> \<alpha>)")
      case True thus ?thesis using J0(1)[of x] \<delta>'_domain unfolding subst_domain_def by auto
    next
      case False
      have "subst_domain I = UNIV" using A unfolding defs by fast
      thus ?thesis using J0(2)[OF False] unfolding subst_domain_def by auto
    qed
    ultimately show ?thesis by auto
  qed
  moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>')"
    using wf_trms_subst_compose[OF subst_var_inv_wf_trms[of \<alpha> "fv s"] \<delta>(2)]
    unfolding \<delta>'_def \<alpha>inv_def by force
  hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range J)" using A J1 unfolding defs by fast
  ultimately show "welltyped_constraint_model J (A@[\<langle>\<star>, send\<langle>[s \<cdot> \<delta>]\<rangle>\<rangle>])" unfolding defs by blast
  hence "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J \<turnstile> s \<cdot> \<delta>"
    using \<delta>_s strand_sem_append_stateful[of "{}" "{}" "unlabel A" "[send\<langle>[s \<cdot> \<delta>]\<rangle>]" J]
    unfolding defs by (simp add: subst_ground_ident)
  moreover have "s \<cdot> \<alpha> \<cdot> J = s \<cdot> \<delta>"
  proof -
    have "J x = \<delta>' x" when x: "x \<in> fv (s \<cdot> \<alpha>)" for x using x unfolding J_def by argo
    hence "s \<cdot> \<alpha> \<cdot> J = s \<cdot> \<alpha> \<cdot> \<delta>'" using subst_agreement[of "s \<cdot> \<alpha>" J \<delta>'] by force
    thus ?thesis
      using \<alpha>_invertible unfolding \<delta>'_def
      by (metis rm_vars_subst_eq' subst_subst_compose)
  qed
  hence "s \<cdot> \<alpha> \<cdot> J = s \<cdot> \<delta>" by auto
  ultimately show "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J \<turnstile> s \<cdot> \<alpha> \<cdot> J" by argo
qed

lemma welltyped_leakage_free_protocol_pointwise:
  "welltyped_leakage_free_protocol S P \<longleftrightarrow> list_all (\<lambda>s. welltyped_leakage_free_protocol [s] P) S"
unfolding welltyped_leakage_free_protocol_def list_all_iff Let_def by fastforce

lemma welltyped_leakage_free_no_deduct_constI:
  fixes c
  defines "s \<equiv> Fun c []::('fun,'atom,'sets,'lbl) prot_term"
  assumes s: "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[s]\<rangle>\<rangle>])"
  shows "welltyped_leakage_free_protocol [s] P"
using s unfolding welltyped_leakage_free_protocol_def s_def by auto

lemma welltyped_leakage_free_pub_termI:
  assumes s: "{} \<turnstile>\<^sub>c s"
  shows "welltyped_leakage_free_protocol [s] P"
proof -
  define Q where "Q \<equiv> \<lambda>M t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}"
  define f where "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. Q M t \<delta>}"
  define Sec where "Sec \<equiv> f (set [s]) - {m. {} \<turnstile>\<^sub>c m}"

  have 0: "fv s = {}" using s pgwt_ground pgwt_is_empty_synth by blast 
  have 1: "s \<cdot> \<delta> = s" for \<delta> by (rule subst_ground_ident[OF 0])
  have 2: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range Var)"
    using wt_subst_Var wf_trm_subst_range_Var by (blast,blast)
  
  have "f (set [s]) = {s}"
  proof
    show "f (set [s]) \<subseteq> {s}" using 0 1 unfolding f_def Q_def by auto 

    have "Q {s} s Var" using 0 2 unfolding Q_def by auto
    thus "{s} \<subseteq> f (set [s])" using 1[of Var] unfolding f_def by force
  qed
  hence "Sec = {}" using s unfolding Sec_def by simp
  thus ?thesis unfolding welltyped_leakage_free_protocol_def Let_def Sec_def f_def Q_def by blast
qed

lemma welltyped_leakage_free_pub_constI:
  assumes c: "public\<^sub>f c" "arity\<^sub>f c = 0"
  shows "welltyped_leakage_free_protocol [\<langle>c\<rangle>\<^sub>c] P"
using c welltyped_leakage_free_pub_termI[OF intruder_synth.ComposeC[of "[]" "Fu c" "{}"]] by simp

lemma welltyped_leakage_free_long_term_secretI:
  fixes n
  defines
      "Tatt \<equiv> \<lambda>s'. Transaction (\<lambda>(). []) [] [\<langle>n, receive\<langle>[s']\<rangle>\<rangle>] [] [] [\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]"
  assumes P_wt_secure:
      "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>.
        welltyped_constraint_model \<I> (\<A>@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
    and s_long_term_secret:
      "\<exists>\<theta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> inj_on \<theta> (fv s) \<and> \<theta> ` fv s \<subseteq> range Var \<and> Tatt (s \<cdot> \<theta>) \<in> set P"
  shows "welltyped_leakage_free_protocol [s] P"
proof (rule ccontr)
  define Q where "Q \<equiv> \<lambda>M t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}"
  define f where "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. Q M t \<delta>}"
  define Sec where "Sec \<equiv> f (set [s]) - {m. {} \<turnstile>\<^sub>c m}"

  note defs = Sec_def f_def Q_def
  note defs' = welltyped_constraint_model_def constraint_model_def

  assume "\<not>welltyped_leakage_free_protocol [s] P"
  then obtain A I s' where A:
      "A \<in> reachable_constraints P" "s' \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I"
      "welltyped_constraint_model I (A@[\<langle>\<star>, send\<langle>[s']\<rangle>\<rangle>])"
    unfolding welltyped_leakage_free_protocol_def defs by fastforce

  obtain \<theta> where \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "\<theta> ` fv s \<subseteq> range Var" "inj_on \<theta> (fv s)" "Tatt (s \<cdot> \<theta>) \<in> set P"
    using s_long_term_secret by blast

  obtain \<delta> where \<delta>:
    "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "subst_domain \<delta> = fv (s \<cdot> \<theta>)" "ground (subst_range \<delta>)"
    "s' = s \<cdot> \<theta> \<cdot> \<delta>"
  proof -
    obtain \<delta> where *: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "fv s' = {}" "s' = s \<cdot> \<delta>"
      using A(2) unfolding defs by auto

    define \<sigma> where "\<sigma> \<equiv> subst_var_inv \<theta> (fv s) \<circ>\<^sub>s \<delta>"
    define \<delta>' where "\<delta>' \<equiv> rm_vars (UNIV - fv (s \<cdot> \<theta>)) \<sigma>"

    have **: "s' = s \<cdot> \<theta> \<cdot> \<sigma>"
      using *(4) inj_var_ran_subst_is_invertible[OF \<theta>(3,2)]
      unfolding \<sigma>_def by simp
    
    have "s' = s \<cdot> \<theta> \<cdot> \<delta>'"
      using ** rm_vars_subst_eq'[of "s \<cdot> \<theta>" \<sigma>]
      unfolding \<delta>'_def by simp
    moreover have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>"
      using \<theta>(1) *(1) subst_var_inv_wt wt_subst_compose
      unfolding \<sigma>_def by presburger
    hence "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>'" using wt_subst_rm_vars unfolding \<delta>'_def by blast
    moreover have "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)"
      using wf_trms_subst_compose[OF subst_var_inv_wf_trms *(2)] unfolding \<sigma>_def by blast
    hence "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>')" using wf_trms_subst_rm_vars'[of \<sigma>] unfolding \<delta>'_def by blast
    moreover have "fv (s \<cdot> \<theta>) \<subseteq> subst_domain \<sigma>"
      using *(3) ** ground_term_subst_domain_fv_subset unfolding \<sigma>_def by blast
    hence "subst_domain \<delta>' = fv (s \<cdot> \<theta>)"
      using rm_vars_dom[of "UNIV - fv (s \<cdot> \<theta>)" \<sigma>] unfolding \<delta>'_def by blast
    moreover have "ground (subst_range \<delta>')"
    proof -
      { fix t assume "t \<in> subst_range \<delta>'"
        then obtain x where "x \<in> fv (s \<cdot> \<theta>)" "\<delta>' x = t"
          using \<open>subst_domain \<delta>' = fv (s \<cdot> \<theta>)\<close> by auto
        hence "t \<sqsubseteq> s \<cdot> \<theta> \<cdot> \<delta>'" by (meson subst_mono_fv)
        hence "fv t = {}" using \<open>s' = s \<cdot> \<theta> \<cdot> \<delta>'\<close> *(3) ground_subterm by blast
      } thus ?thesis by force
    qed
    ultimately show thesis using that[of \<delta>'] by fast
  qed

  have \<xi>: "transaction_decl_subst Var (Tatt t)"
    and \<sigma>: "transaction_fresh_subst Var (Tatt t) A"
    for t
    unfolding transaction_decl_subst_def transaction_fresh_subst_def Tatt_def by simp_all

  obtain \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
    where \<alpha>: "transaction_renaming_subst \<alpha> P A"
    unfolding transaction_renaming_subst_def by blast

  obtain J where J:
      "welltyped_constraint_model J (A@[\<langle>\<star>, send\<langle>[s \<cdot> \<theta> \<cdot> \<delta>]\<rangle>\<rangle>])" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J \<turnstile> s \<cdot> \<theta> \<cdot> \<alpha> \<cdot> J"
    using welltyped_constraint_model_leakage_model_swap[OF A(3)[unfolded \<delta>(5)] \<alpha> \<delta>(1-4)] by blast

  define T where "T = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand (Tatt (s \<cdot> \<theta>)) \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>)"
  define B where "B \<equiv> A@T"

  have "transaction_receive (Tatt t) = [\<langle>n, receive\<langle>[t]\<rangle>\<rangle>]"
       "transaction_checks (Tatt t) = []"
       "transaction_updates (Tatt t) = []"
       "transaction_send (Tatt t) = [\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]"
    for t
    unfolding Tatt_def by simp_all
  hence T_def': "T = [\<langle>n, send\<langle>[s \<cdot> \<theta> \<cdot> \<alpha>]\<rangle>\<rangle>, \<langle>n, receive\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]"
    using subst_lsst_append[of "transaction_receive (Tatt (s \<cdot> \<theta>))" _ \<alpha>]
          subst_lsst_singleton[of "ln n" "receive\<langle>[s \<cdot> \<theta>]\<rangle>" \<alpha>]
          subst_lsst_singleton[of "ln n" "send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>" \<alpha>]
    unfolding transaction_strand_def T_def by fastforce
  
  have B0: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t B \<cdot>\<^sub>s\<^sub>e\<^sub>t J \<turnstile> attack\<langle>ln n\<rangle>"
    using in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of "attack\<langle>ln n\<rangle>" "unlabel T"]
    unfolding B_def T_def' by (force intro!: intruder_deduct.Axiom)

  have B1: "B \<in> reachable_constraints P"
    using reachable_constraints.step[OF A(1) \<theta>(4) \<xi> \<sigma> \<alpha>]
    unfolding B_def T_def by simp

  have "welltyped_constraint_model J B"
    using J strand_sem_append_stateful[of "{}" "{}" "unlabel A" _ J]
    unfolding defs' B_def T_def' by fastforce
  hence B2: "welltyped_constraint_model J (B@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
    using B0 strand_sem_append_stateful[of "{}" "{}" "unlabel B" "[send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>]" J]
    unfolding defs' B_def by auto

  show False using P_wt_secure B1 B2 by blast
qed

lemma welltyped_leakage_free_value_constI:
  assumes P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. admissible_transaction_terms T"
      "\<forall>T \<in> set P. transaction_decl T () = []"
      "\<forall>T \<in> set P. bvars_transaction T = {}"
    and P_fresh_declass:
      "\<forall>T \<in> set P. transaction_fresh T \<noteq> [] \<longrightarrow>
        (transaction_send T \<noteq> [] \<and> (let (l,a) = hd (transaction_send T)
          in l = \<star> \<and> is_Send a \<and> Var ` set (transaction_fresh T) \<subseteq> set (the_msgs a)))"
  shows "welltyped_leakage_free_protocol [\<langle>m: value\<rangle>\<^sub>v] P"
proof (rule ccontr)
  define Q where "Q \<equiv> \<lambda>M t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}"
  define f where "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. Q M t \<delta>}"
  define Sec where "Sec \<equiv> f (set [\<langle>m: value\<rangle>\<^sub>v]) - {m. {} \<turnstile>\<^sub>c m}"

  note defs = Sec_def f_def Q_def
  note defs' = welltyped_constraint_model_def constraint_model_def

  assume "\<not>welltyped_leakage_free_protocol [\<langle>m: value\<rangle>\<^sub>v] P"
  then obtain A I s where A:
      "A \<in> reachable_constraints P" "s \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I"
      "welltyped_constraint_model I (A@[\<langle>\<star>, send\<langle>[s]\<rangle>\<rangle>])"
    unfolding welltyped_leakage_free_protocol_def defs by fastforce

  have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> s \<cdot> I" using welltyped_constraint_model_deduct_split[OF A(3)] by simp
  moreover have "s \<cdot> I = s" using A(2) unfolding defs by fast
  ultimately have s_deduct: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I) \<turnstile> s" by (metis ik\<^sub>s\<^sub>s\<^sub>t_subst unlabel_subst)

  note I0 = welltyped_constraint_model_prefix[OF A(3)]

  have I1: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" using A(3) unfolding defs' by blast

  obtain f ts \<delta> where f: "s = Fun f ts" "s = \<langle>m: value\<rangle>\<^sub>v \<cdot> \<delta>" "\<not>{} \<turnstile>\<^sub>c s" "s \<notin> declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I"
      and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "fv s = {}"
    using A(2) unfolding defs by (cases s) auto

  have s1: "\<Gamma> s = TAtom Value"
    by (metis \<Gamma>.simps(1) \<Gamma>\<^sub>v_TAtom f(2) wt_subst_trm''[OF \<delta>(1)]) 

  have s2: "wf\<^sub>t\<^sub>r\<^sub>m s"
    using f(2) \<delta>(2) by force
  
  have s3: "ts = []"
    using f(1) s1 s2 const_type_inv_wf by blast

  obtain sn where sn: "s = Fun (Val sn) []"
    using s1 f(3) \<Gamma>_Fu_simps(4) \<Gamma>_Set_simps(3) unfolding f(1) s3 by (cases f) auto

  have "s \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
    using private_fun_deduct_in_ik'[OF s_deduct[unfolded sn]]
    by (metis sn public.simps(3) ik\<^sub>s\<^sub>s\<^sub>t_subst unlabel_subst)
  hence s4: "s \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
    using constraint_model_Val_const_in_constr_prefix[OF A(1) I0 P(1,2)]
    unfolding sn by presburger

  obtain B T \<xi> \<sigma> \<alpha> where B:
      "prefix (B@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) A"
      "B \<in> reachable_constraints P" "T \<in> set P" "transaction_decl_subst \<xi> T"
      "transaction_fresh_subst \<sigma> T B" "transaction_renaming_subst \<alpha> P B"
      "s \<in> subst_range \<sigma>"
    using constraint_model_Value_in_constr_prefix_fresh_action'[OF A(1) P(2-) s4[unfolded sn]] sn
    by blast

  obtain Tts Tsnds sx
    where T: "transaction_send T = \<langle>\<star>, send\<langle>Tts\<rangle>\<rangle>#Tsnds" "Var ` set (transaction_fresh T) \<subseteq> set Tts"
      and sx: "Var sx \<in> set Tts" "\<sigma> sx = s"
    using P_fresh_declass B(3,5,7)
    unfolding transaction_fresh_subst_def is_Send_def
    by (cases "transaction_send T") (fastforce,fastforce)

  have \<xi>_elim: "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> = \<sigma> \<circ>\<^sub>s \<alpha>"
    using admissible_transaction_decl_subst_empty'[OF bspec[OF P(3) B(3)] B(4)]
    by simp

  have s5: "s \<in> set (Tts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s I)"
    using sx unfolding \<xi>_elim sn by force

  have s6: "\<langle>\<star>, receive\<langle>Tts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha> \<circ>\<^sub>s I\<rangle>\<rangle> \<in> set (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)"
  proof -
    have "\<langle>\<star>, send\<langle>Tts\<rangle>\<rangle> \<in> set (transaction_send T)"
      using T(1) by simp
    hence "\<langle>\<star>, send\<langle>Tts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>\<rangle>\<rangle> \<in> set (transaction_send T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)" for \<delta>
      unfolding subst_apply_labeled_stateful_strand_def by force
    hence "\<langle>\<star>, send\<langle>Tts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>\<rangle>\<rangle> \<in> set (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>)" for \<delta>
      using transaction_strand_subst_subsets(4)[of T \<delta>] by fast
    hence *: "\<langle>\<star>, receive\<langle>Tts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>\<rangle>\<rangle> \<in> set (dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<delta>))" for \<delta>
      using dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(1)[of \<star> "Tts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>"] by blast

    have "\<langle>\<star>, receive\<langle>Tts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>\<rangle>\<rangle> \<in> set A"
      using B(1) *[of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] unfolding prefix_def by force
    thus ?thesis
      unfolding subst_apply_labeled_stateful_strand_def by force
  qed

  show False
    using s6 f(4) ideduct_mono[OF Axiom[OF s5], of "\<Union>{set ts|ts. \<langle>\<star>,receive\<langle>ts\<rangle>\<rangle> \<in> set (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)}"]
    unfolding declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by blast
qed

lemma welltyped_leakage_free_priv_constI:
  fixes c
  defines "s \<equiv> Fun c []::('fun,'atom,'sets,'lbl) prot_term"
  assumes c: "\<not>public c" "arity c = 0" "\<Gamma> s = TAtom ca" "ca \<noteq> Value"
    and P: "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. is_Var (\<Gamma>\<^sub>v x)"
           "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T \<union> set (transaction_fresh T). \<Gamma> s \<noteq> \<Gamma>\<^sub>v x"
           "\<forall>T \<in> set P. \<forall>t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). s \<notin> set (snd (Ana t))"
           "\<forall>T \<in> set P. s \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
           "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
           "\<forall>T \<in> set P. wellformed_transaction T"
   shows "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[s]\<rangle>\<rangle>])"
          (is "\<forall>\<A> \<in> ?R. ?P \<A>")
     and "welltyped_leakage_free_protocol [s] P"
proof -
  show "\<forall>\<A> \<in> ?R. ?P \<A>"
  proof
    fix A assume A: "A \<in> reachable_constraints P"
  
    define Q where "Q \<equiv> \<lambda>M t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}"
    define f where "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. Q M t \<delta>}"
    define Sec where "Sec \<equiv> f (set [s]) - {m. {} \<turnstile>\<^sub>c m}"
    
    define f' where "f' \<equiv> \<lambda>(T,\<xi>,\<sigma>::('fun,'atom,'sets,'lbl) prot_subst,\<alpha>).
                              dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
    define g' where "g' \<equiv> concat \<circ> map f'"

    let ?P_s_cases = "\<lambda>M. s \<in> M \<or> (\<exists>m \<in> subterms\<^sub>s\<^sub>e\<^sub>t M. s \<in> set (snd (Ana m)))"
    let ?P_s_cases' = "\<lambda>M \<delta>. s \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<or> (\<exists>m \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>. s \<in> set (snd (Ana m)))"

    note defs = Sec_def f_def Q_def
    note defs' = welltyped_constraint_model_def constraint_model_def
  
    show "?P A"
    proof (rule ccontr)
      assume "\<not>?P A"
      then obtain I where I: "welltyped_constraint_model I (A@[\<langle>\<star>, send\<langle>[s]\<rangle>\<rangle>])" by blast
  
      obtain Ts where Ts:
          "A = g' Ts" "\<forall>B. prefix B Ts \<longrightarrow> g' B \<in> reachable_constraints P"
          "\<forall>B T \<xi> \<sigma> \<alpha>. prefix (B@[(T,\<xi>,\<sigma>,\<alpha>)]) Ts \<longrightarrow>
                T \<in> set P \<and> transaction_decl_subst \<xi> T \<and>
                transaction_fresh_subst \<sigma> T (g' B) \<and> transaction_renaming_subst \<alpha> P (g' B)"
        using reachable_constraints_as_transaction_lists[OF A(1)] unfolding g'_def f'_def by blast
    
      have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> s \<cdot> I" and I_s: "s \<cdot> I = s"
        using welltyped_constraint_model_deduct_split[OF I]
        unfolding s_def by simp_all
      hence s_deduct: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I) \<turnstile> s" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> s"
        by (metis ik\<^sub>s\<^sub>s\<^sub>t_subst unlabel_subst, metis)
    
      have I_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
          and I_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
          and I_grounds: "ground (subst_range I)"
          and I_interp: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I"
        using I unfolding defs' by (blast,blast,blast,blast)
    
      have Sec_unfold: "Sec = {s}"
      proof
        have "\<not>{} \<turnstile>\<^sub>c s" using ideduct_synth_priv_const_in_ik[OF _ c(1)] unfolding s_def by blast
        thus "{s} \<subseteq> Sec" unfolding defs s_def by fastforce
      qed (auto simp add: defs s_def)
    
      have s2: "wf\<^sub>t\<^sub>r\<^sub>m s"
        using c(1,2) unfolding s_def by fastforce
    
      have A_ik_fv: "\<exists>a. \<Gamma>\<^sub>v x = TAtom a \<and> a \<noteq> ca" when x: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" for x
      proof -
        obtain T where T: "T \<in> set P" "\<Gamma>\<^sub>v x \<in> \<Gamma>\<^sub>v ` fv_transaction T"
          using fv_ik\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t[OF x] reachable_constraints_var_types_in_transactions(1)[OF A P(5)]
          by fast
        then obtain y where y: "y \<in> vars_transaction T" "\<Gamma>\<^sub>v y = \<Gamma>\<^sub>v x"
          using vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel (transaction_strand T)"] by fastforce
        then obtain a where a: "\<Gamma>\<^sub>v y = TAtom a" using P(1) T(1) by blast
        hence "\<Gamma>\<^sub>v x = TAtom a" "\<Gamma> s \<noteq> \<Gamma>\<^sub>v x" "\<Gamma> s = TAtom ca" using y P(2) T(1) c(3) by auto
        thus ?thesis by force
      qed
    
      have I_s_x: "\<not>s \<sqsubseteq> I x" when x: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" for x
      proof -
        obtain a where a: "\<Gamma>\<^sub>v x = TAtom a" "a \<noteq> ca" using A_ik_fv[OF x] by blast
        hence a': "\<Gamma> (I x) = TAtom a" using wt_subst_trm''[OF I_wt, of "Var x"] by simp
        
        obtain f ts where f: "I x = Fun f ts"
          by (meson empty_fv_exists_fun interpretation_grounds_all[OF I_interp])
        hence ts: "ts = []"
          using I_wf const_type_inv_wf[OF a'[unfolded f]] by fastforce
    
        have "c \<noteq> f" using f[unfolded ts] a a' c(3)[unfolded s_def] by force
        thus ?thesis using f ts unfolding s_def by simp
      qed
    
      have A_ik_I_const: "\<exists>f. arity f = 0 \<and> I x = Fun f []" when x: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" for x
        using x A_ik_fv I_wt empty_fv_exists_fun[OF interpretation_grounds_all[OF I_interp, of x]]
              wf_trm_subst_rangeD[OF I_wf, of x] const_type_inv const_type_inv_wf
        by (metis (no_types, lifting) \<Gamma>.simps(1) wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
      hence A_ik_subst: "subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) = subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
        using subterms_subst''[of "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" I] by blast
    
      have sublmm1: "s \<in> set (snd (Ana m))"
        when m: "m \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t M" "s \<in> set (snd (Ana (m \<cdot> \<delta>)))"
          and M: "\<And>y. y \<in> fv\<^sub>s\<^sub>e\<^sub>t M \<Longrightarrow> \<not>s \<sqsubseteq> \<delta> y"
        for m M \<delta>
      proof -
        have m_fun: "is_Fun m"
          using m M Ana_subterm' vars_iff_subtermeq_set
          unfolding s_def is_Var_def by (metis subst_apply_term.simps(1))
        
        obtain f K R ts i where f:
            "m = \<langle>f ts\<rangle>\<^sub>t" "arity\<^sub>f f = length ts" "arity\<^sub>f f > 0" "Ana\<^sub>f f = (K, R)"
          and i: "i < length R" "s = ts ! (R ! i) \<cdot> \<delta>"
          and R_i: "\<forall>i < length R. map ((!) ts) R ! i = ts ! (R ! i) \<and> R ! i < length ts"
        proof -
          obtain f ts K R where f:
              "m \<cdot> \<delta> = \<langle>f ts\<rangle>\<^sub>t" "arity\<^sub>f f = length ts" "arity\<^sub>f f > 0"
              "Ana\<^sub>f f = (K, R)" "Ana (m \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) ts, map ((!) ts) R)"
            using m(2) Ana_nonempty_inv[of "m \<cdot> \<delta>"] by force
      
          obtain ts' where m': "m = \<langle>f ts'\<rangle>\<^sub>t" "ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>"
            using f(1) m_fun by auto
      
          have R_i: "map ((!) ts) R ! i = ts ! (R ! i)" "R ! i < length ts"
            when i: "i < length R" for i
            using i Ana\<^sub>f_assm2_alt[OF f(4), of "R ! i"] f(2) by simp_all
          then obtain i where i: "s = ts ! (R ! i)" "i < length R"
            by (metis (no_types, lifting) m(2) f(5) in_set_conv_nth length_map snd_conv)
      
          have ts': "arity\<^sub>f f = length ts'" "length ts = length ts'" using m'(2) f(2) by simp_all
      
          have s': "s = ts' ! (R ! i) \<cdot> \<delta>" using R_i(2)[OF i(2)] i(1) unfolding ts'(2) m'(2) by simp
      
          show thesis using that f m' R_i ts' s' i by auto
        qed
    
        have "s = ts ! (R ! i)"
        proof (cases "ts ! (R ! i)")
          case (Var x)
          hence "Var x \<in> set ts" using R_i i nth_mem by fastforce
          hence "x \<in> fv\<^sub>s\<^sub>e\<^sub>t M" using m(1) f(1) fv_subterms_set by fastforce
          thus ?thesis using i M Var by fastforce
        qed (use i s_def in fastforce)
        thus "s \<in> set (snd (Ana m))" using f(1) Ana_Fu_intro[OF f(2-4)] i(1) by simp
      qed
    
      have "\<not>s \<sqsubseteq> \<delta> y"
        when m: "m \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "s \<in> set (snd (Ana (m \<cdot> \<delta>)))"
          and T: "T \<in> set P" and \<delta>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
          and \<delta>_ran: "\<And>t. t \<in> subst_range \<delta> \<Longrightarrow> (\<exists>c. t = Fun c [] \<and> arity c = 0) \<or> (\<exists>x. t = Var x)"
          and y: "y \<in> fv\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))"
        for m T \<delta> y
      proof
        assume "s \<sqsubseteq> \<delta> y"
        hence "\<Gamma>\<^sub>v y = \<Gamma> s" using wt_subst_trm''[OF \<delta>_wt, of "Var y"] \<delta>_ran[of "\<delta> y"] by fastforce
        moreover have "y \<in> vars_transaction T"
          using y trms\<^sub>s\<^sub>s\<^sub>t_fv_vars\<^sub>s\<^sub>s\<^sub>t_subset unfolding vars_transaction_unfold[of T] by fastforce
        ultimately show False using P(2) T by force
      qed
      hence sublmm2: "s \<in> set (snd (Ana m))"
        when m: "m \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "s \<in> set (snd (Ana (m \<cdot> \<delta>)))"
          and T: "T \<in> set P" and \<delta>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
          and \<delta>_ran: "\<And>t. t \<in> subst_range \<delta> \<Longrightarrow> (\<exists>c. t = Fun c [] \<and> arity c = 0) \<or> (\<exists>x. t = Var x)"
        for m T \<delta>
        using sublmm1[OF m] m T \<delta>_wt \<delta>_ran by blast

      have "s \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<or> (\<exists>m \<in> subterms\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<cdot>\<^sub>s\<^sub>e\<^sub>t I. s \<in> set (snd (Ana m)))"
        using private_const_deduct[OF c(1) s_deduct(2)[unfolded s_def]]
              I_s_x const_mem_subst_cases[of c] A_ik_subst
        unfolding s_def by blast
      hence "?P_s_cases (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" using sublmm1[of _ "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"] I_s_x by blast
      then obtain T \<xi> \<sigma> \<alpha> where T: "(T,\<xi>,\<sigma>,\<alpha>) \<in> set Ts" "?P_s_cases (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t (f' (T,\<xi>,\<sigma>,\<alpha>)))"
        using ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t_concat[of "map f' Ts"] Ts(1)[unfolded g'_def] by fastforce
    
      obtain B where "prefix (B@[(T, \<xi>, \<sigma>, \<alpha>)]) Ts" by (metis T(1) prefix_snoc_in_iff)
      hence T_in_P: "T \<in> set P"
          and T_wf: "wellformed_transaction T"
          and \<xi>: "transaction_decl_subst \<xi> T"
          and \<sigma>: "transaction_fresh_subst \<sigma> T (concat (map f' B))"
          and \<alpha>: "transaction_renaming_subst \<alpha> P (concat (map f' B))"
        using P(6) Ts(3)[unfolded g'_def] unfolding comp_def by (metis,metis,metis,metis,metis)
    
      note \<xi>\<sigma>\<alpha>_wt = transaction_decl_fresh_renaming_substs_wt[OF \<xi> \<sigma> \<alpha>]
      note \<xi>\<sigma>\<alpha>_ran = transaction_decl_fresh_renaming_substs_range'(1)[OF \<xi> \<sigma> \<alpha>]
    
      have "subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>) = subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" for M
        using \<xi>\<sigma>\<alpha>_ran subterms_subst''[of _ "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"] by (meson subst_imgI)
      hence s_cases: "?P_s_cases' (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) (\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
        using T(2) dual_transaction_ik_is_transaction_send'[OF T_wf, of "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
        unfolding f'_def by auto
    
      from s_cases show False
      proof
        assume "s \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
        then obtain t where t: "t \<in> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" "s = t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>" by moura
        have "s \<noteq> t" using P(4) T_in_P t(1) by blast
        then obtain x where x: "t = Var x" using t(2) unfolding s_def by (cases t) auto
        
        have "\<Gamma>\<^sub>v x = \<Gamma> s" using x t(2) wt_subst_trm''[OF \<xi>\<sigma>\<alpha>_wt, of "Var x"] by simp
        moreover have "x \<in> vars_transaction T"
          using t(1) trms\<^sub>s\<^sub>s\<^sub>t_fv_vars\<^sub>s\<^sub>s\<^sub>t_subset unfolding x vars_transaction_unfold[of T] by fastforce
        ultimately show False using P(2) T_in_P by force
      qed (use sublmm2[OF _ _ T_in_P \<xi>\<sigma>\<alpha>_wt \<xi>\<sigma>\<alpha>_ran] P(3) T_in_P in blast)
    qed
  qed
  thus "welltyped_leakage_free_protocol [s] P"
    using welltyped_leakage_free_no_deduct_constI[of P c]
    unfolding s_def by blast
qed

lemma welltyped_leakage_free_priv_constI':
  assumes c: "\<not>public\<^sub>f c" "arity\<^sub>f c = 0" "\<Gamma>\<^sub>f c = Some ca"
    and P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T \<union> set (transaction_fresh T). \<Gamma> \<langle>c\<rangle>\<^sub>c \<noteq> \<Gamma>\<^sub>v x"
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. is_Var (\<Gamma>\<^sub>v x)"
      "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
      "\<forall>T \<in> set P. \<forall>t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). \<langle>c\<rangle>\<^sub>c \<notin> set (snd (Ana t))"
      "\<forall>T \<in> set P. \<langle>c\<rangle>\<^sub>c \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
   shows "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[\<langle>c\<rangle>\<^sub>c]\<rangle>\<rangle>])"
     and "welltyped_leakage_free_protocol [\<langle>c\<rangle>\<^sub>c] P"
using c welltyped_leakage_free_priv_constI[OF _ _ _ _ P(3,2,5,6,4,1), of "Atom ca"]
by (force, force)

lemma welltyped_leakage_free_set_constI:
  assumes P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. \<forall>f \<in> \<Union>(funs_term ` (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))). \<not>is_Set f"
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T \<union> set (transaction_fresh T). \<Gamma>\<^sub>v x \<noteq> TAtom SetType"
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. is_Var (\<Gamma>\<^sub>v x)"
      "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
    and c: "arity\<^sub>s c = 0"
  shows "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[\<langle>c\<rangle>\<^sub>s]\<rangle>\<rangle>])"
    and "welltyped_leakage_free_protocol [\<langle>c\<rangle>\<^sub>s] P"
proof -
  have c'': "\<langle>c\<rangle>\<^sub>s \<notin> subterms t"
    when T: "T \<in> set P" and t: "t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)" for T t
    using t bspec[OF P(2) T] subtermeq_imp_funs_term_subset[of t]
          funs_term_Fun_subterm'[of "Set c" "[]::('fun,'atom,'sets,'lbl) prot_term list"]
    by fastforce

  have P':
      "\<forall>T \<in> set P. \<forall>t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). \<langle>c\<rangle>\<^sub>s \<notin> set (snd (Ana t))"
      "\<forall>T \<in> set P. \<langle>c\<rangle>\<^sub>s \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
    subgoal using Ana_subterm' c'' by fast
    subgoal using c'' by fast
    done

  have P'':
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T \<union> set (transaction_fresh T). \<Gamma> \<langle>c\<rangle>\<^sub>s \<noteq> \<Gamma>\<^sub>v x"
    using P(3) \<Gamma>_consts_simps(4)[OF c] by fastforce

  show "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[\<langle>c\<rangle>\<^sub>s]\<rangle>\<rangle>])"
       "welltyped_leakage_free_protocol [\<langle>c\<rangle>\<^sub>s] P"
    using c welltyped_leakage_free_priv_constI[OF _ _ _ _ P(4) P'' P' P(5,1), of SetType]
    by (force, force)
qed

lemma welltyped_leakage_free_occurssec_constI:
  defines "s \<equiv> Fun OccursSec []"
  assumes P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T \<union> set (transaction_fresh T). \<Gamma>\<^sub>v x \<noteq> TAtom OccursSecType"
      "\<forall>T \<in> set P. \<forall>t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). Fun OccursSec [] \<notin> set (snd (Ana t))"
      "\<forall>T \<in> set P. Fun OccursSec [] \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. is_Var (\<Gamma>\<^sub>v x)"
      "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
  shows "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[s]\<rangle>\<rangle>])"
    and "welltyped_leakage_free_protocol [s] P"
proof -
  have P':
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T \<union> set (transaction_fresh T). \<Gamma> (Fun OccursSec []) \<noteq> \<Gamma>\<^sub>v x"
    using P(2) by auto

  show "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[s]\<rangle>\<rangle>])"
       "welltyped_leakage_free_protocol [s] P"
    using welltyped_leakage_free_priv_constI[OF _ _ _ _ P(5) P' P(3,4,6,1), of OccursSecType]
    unfolding s_def by auto
qed

lemma welltyped_leakage_free_occurs_factI:
  assumes P: "\<forall>T \<in> set P. admissible_transaction T"
    and P_occ_star:
      "\<forall>T \<in> set P. \<forall>r \<in> set (transaction_send T).
        OccursFact \<in> \<Union>(funs_term ` (trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd r))) \<longrightarrow> fst r = \<star>"
  shows "welltyped_leakage_free_protocol [occurs x] P"
proof -
  define Q where "Q \<equiv> \<lambda>M t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}"
  define f where "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. Q M t \<delta>}"
  define Sec where "Sec \<equiv> f (set [occurs x]) - {m. {} \<turnstile>\<^sub>c m}"

  define f' where "f' \<equiv> \<lambda>(T,\<xi>,\<sigma>::('fun,'atom,'sets,'lbl) prot_subst,\<alpha>).
                            dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  define g' where "g' \<equiv> concat \<circ> map f'"

  note defs = Sec_def f_def Q_def
  note defs' = welltyped_constraint_model_def constraint_model_def

  show ?thesis
  proof (rule ccontr)
    assume "\<not>welltyped_leakage_free_protocol [occurs x] P"
    then obtain A I k where A:
        "A \<in> reachable_constraints P" "occurs k \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I"
        "welltyped_constraint_model I (A@[\<langle>\<star>, send\<langle>[occurs k]\<rangle>\<rangle>])"
      unfolding welltyped_leakage_free_protocol_def defs by fastforce

    note A' = welltyped_constraint_model_prefix[OF A(3)]

    have occ_I: "occurs k \<cdot> I = occurs k" using A(2) unfolding defs by auto
    hence occ_in_ik: "occurs k \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" "occurs k \<in> ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      using welltyped_constraint_model_deduct_split(2)[OF A(3)]
            reachable_constraints_occurs_fact_deduct_in_ik[OF A(1) A' P, of k]
      by (argo, argo)
    then obtain l ts where ts: "(l,receive\<langle>ts\<rangle>) \<in> set A" "occurs k \<in> set ts"
      using in_ik\<^sub>s\<^sub>s\<^sub>t_iff[of "occurs k" "unlabel A"] unfolding unlabel_def by moura

    obtain T a B \<alpha> \<sigma> \<xi>
      where B: "prefix (B@f' (T,\<xi>,\<sigma>,\<alpha>)) A"
        and T: "T \<in> set P" "transaction_decl_subst \<xi> T" "transaction_fresh_subst \<sigma> T B"
               "transaction_renaming_subst \<alpha> P B"
        and a: "a \<in> set (transaction_strand T)" "fst (l,receive\<langle>ts\<rangle>) = fst a"
               "(l,receive\<langle>ts\<rangle>) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p a \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      using reachable_constraints_transaction_action_obtain[OF A(1) ts(1), of thesis]
      unfolding f'_def by simp

    obtain ts' where ts': "a = (l,send\<langle>ts'\<rangle>)" "ts = ts' \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      using surj_pair[of a] a(2,3) by (cases "snd a") force+

    obtain t where t: "t \<in> set ts'" "occurs k = t \<cdot> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
      using ts(2) unfolding ts'(2) by force

    have occ_t: "OccursFact \<in> funs_term t"
    proof (cases t)
      case (Var y) thus ?thesis
        using t(2) subst_apply_term.simps(1)[of y "\<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"]
              transaction_decl_fresh_renaming_substs_range'(1)[OF T(2-), of "occurs k"]
        by fastforce
    qed (use t(2) in simp)

    have P_wf: "\<forall>T \<in> set P. wellformed_transaction T"
      using P admissible_transaction_is_wellformed_transaction(1) by blast

    have l: "l = \<star>"
      using wellformed_transaction_strand_memberD(8)[OF bspec[OF P_wf T(1)] a(1)[unfolded ts'(1)]]
            t(1) T(1) P_occ_star occ_t
      unfolding ts'(1) by fastforce

    have "occurs k \<in> \<Union>{set ts |ts. \<langle>\<star>, receive\<langle>ts\<rangle>\<rangle> \<in> set (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)}"
      using subst_lsst_memI[OF ts(1), of I] subst_set_map[OF ts(2), of I]
      unfolding occ_I l by auto
    thus False using A(2) unfolding declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by simp
  qed
qed

lemma welltyped_leakage_free_setop_pairI:
  assumes P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
      "\<forall>T \<in> set P. \<forall>f \<in> \<Union>(funs_term ` (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T))). \<not>is_Set f"
      "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
      "\<forall>T \<in> set P. transaction_decl T () = []"
      "\<forall>T \<in> set P. admissible_transaction_terms T"
    and c: "arity\<^sub>s c = 0"
  shows "welltyped_leakage_free_protocol [pair (x, \<langle>c\<rangle>\<^sub>s)] P"
proof -
  define Q where "Q \<equiv> \<lambda>M t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}"
  define f where "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. Q M t \<delta>}"
  define Sec where "Sec \<equiv> f (set [pair (x, \<langle>c\<rangle>\<^sub>s)]) - {m. {} \<turnstile>\<^sub>c m}"

  define f' where "f' \<equiv> \<lambda>(T,\<xi>,\<sigma>::('fun,'atom,'sets,'lbl) prot_subst,\<alpha>).
                            dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  define g' where "g' \<equiv> concat \<circ> map f'"

  note defs = Sec_def f_def Q_def
  note defs' = welltyped_constraint_model_def constraint_model_def

  have P':
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T \<union> set (transaction_fresh T). \<Gamma>\<^sub>v x \<noteq> TAtom SetType"
      "\<forall>T \<in> set P. \<forall>x \<in> vars_transaction T. is_Var (\<Gamma>\<^sub>v x)"
      "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
    subgoal using P(2,4) by fastforce
    subgoal using P(2) by fastforce
    subgoal using P(4) by fast
    done

  note 0 = welltyped_leakage_free_set_constI(1)[OF P(1,3) P' c]

  show ?thesis
  proof (rule ccontr)
    assume "\<not>welltyped_leakage_free_protocol [pair (x, \<langle>c\<rangle>\<^sub>s)] P"
    then obtain A I k where A:
        "A \<in> reachable_constraints P" "pair (k, \<langle>c\<rangle>\<^sub>s) \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I"
        "welltyped_constraint_model I (A@[\<langle>\<star>, send\<langle>[pair (k, \<langle>c\<rangle>\<^sub>s)]\<rangle>\<rangle>])"
      unfolding welltyped_leakage_free_protocol_def defs pair_def by fastforce

    note A' = welltyped_constraint_model_prefix[OF A(3)]

    have "pair (k, \<langle>c\<rangle>\<^sub>s) \<cdot> I = pair (k, \<langle>c\<rangle>\<^sub>s)" using A(2) unfolding defs by auto
    hence "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> pair (k, \<langle>c\<rangle>\<^sub>s)"
      using welltyped_constraint_model_deduct_split(2)[OF A(3)] by argo
    then obtain n where n: "intruder_deduct_num (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) n (pair (k, \<langle>c\<rangle>\<^sub>s))"
      using deduct_num_if_deduct by fast

    have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<subseteq> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      using A(3) ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset unfolding defs' by simp_all
    hence "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<subseteq> SMP (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)" by blast
    hence "Pair \<notin> \<Union>(funs_term ` (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I))"
      using reachable_constraints_no_Pair_fun'[OF A(1) P(4-6)] P by blast
    hence 1: "\<not>pair (k, \<langle>c\<rangle>\<^sub>s) \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      using funs_term_Fun_subterm'[of Pair] unfolding pair_def by auto
    
    have 2: "pair (k, \<langle>c\<rangle>\<^sub>s) \<notin> set (snd (Ana m))" when m: "m \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I" for m
      using m 1 term.dual_order.trans Ana_subterm'[of "pair (k, \<langle>c\<rangle>\<^sub>s)" m] by auto

    have "\<not>ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> \<langle>c\<rangle>\<^sub>s"
      using 0 A(1) A' welltyped_constraint_model_deduct_iff[of I A \<star> "\<langle>c\<rangle>\<^sub>s"] by force
    moreover have "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> \<langle>c\<rangle>\<^sub>s"
      using 1 2 deduct_inv[OF n] deduct_if_deduct_num[of "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I" _ "\<langle>c\<rangle>\<^sub>s"]
      unfolding pair_def by auto
    ultimately show False by blast
  qed
qed

lemma welltyped_leakage_free_short_term_secretI:
  fixes c x y f n d l l'
  defines "s \<equiv> \<langle>f [\<langle>c\<rangle>\<^sub>c, \<langle>x: value\<rangle>\<^sub>v]\<rangle>\<^sub>t"
    and "Tatt \<equiv> Transaction (\<lambda>(). []) []
          [\<langle>\<star>, receive\<langle>[occurs \<langle>y: value\<rangle>\<^sub>v]\<rangle>\<rangle>,
           (l, receive\<langle>[\<langle>f [\<langle>c\<rangle>\<^sub>c, \<langle>y: value\<rangle>\<^sub>v]\<rangle>\<^sub>t]\<rangle>)]
          [(l', \<langle>\<langle>y: value\<rangle>\<^sub>v not in \<langle>d\<rangle>\<^sub>s\<rangle>)]
          []
          [\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]"
  assumes P:
      "\<forall>T \<in> set P. admissible_transaction T"
      "\<forall>T \<in> set P. \<forall>x \<in> set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
    and subterms_sec:
      "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[\<langle>c\<rangle>\<^sub>c]\<rangle>\<rangle>])"
    and P_sec:
      "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>.
        welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
    and P_Tatt: "Tatt \<in> set P"
    and P_d:
      "\<forall>T \<in> set P. \<forall>a \<in> set (transaction_updates T).
        is_Insert (snd a) \<and> the_set_term (snd a) = \<langle>d\<rangle>\<^sub>s \<longrightarrow>
          transaction_send T \<noteq> [] \<and> (let (l,b) = hd (transaction_send T)
            in l = \<star> \<and> is_Send b \<and> \<langle>f [\<langle>c\<rangle>\<^sub>c, the_elem_term (snd a)]\<rangle>\<^sub>t \<in> set (the_msgs b))"
  shows "welltyped_leakage_free_protocol [s] P"
proof -
  define Q where "Q \<equiv> \<lambda>M t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}"
  define Sec where "Sec \<equiv> {t \<cdot> \<delta> | t \<delta>. Q (set [s]) t \<delta>} - {m. {} \<turnstile>\<^sub>c m}"

  define f' where "f' \<equiv> \<lambda>(T,\<xi>,\<sigma>::('fun,'atom,'sets,'lbl) prot_subst,\<alpha>).
                            dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  define g' where "g' \<equiv> concat \<circ> map f'"

  note defs = Sec_def Q_def
  note defs' = welltyped_constraint_model_def constraint_model_def

  show ?thesis
  proof (rule ccontr)
    assume "\<not>welltyped_leakage_free_protocol [s] P"
    then obtain A I k where A:
        "A \<in> reachable_constraints P" "\<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I"
        "welltyped_constraint_model I (A@[\<langle>\<star>, send\<langle>[\<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t]\<rangle>\<rangle>])"
      unfolding welltyped_leakage_free_protocol_def defs s_def by fastforce

    have I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
      using A(3) unfolding defs' by (blast,blast,blast)

    note A' = welltyped_constraint_model_prefix[OF A(3)]

    have "strand_sem_stateful {} {} (unlabel A) I"
      using A' unfolding defs' by simp
    hence A'': "strand_sem_stateful {} {} (unlabel A) (I(z := k))"
      when z: "z \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" for z
      using z strand_sem_model_swap[of "unlabel A" I "I(z := k)" "{}" "{}"] by auto

    obtain \<delta> where \<delta>:
        "\<delta> (the_Var \<langle>x: value\<rangle>\<^sub>v) = k" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
        "fv (\<delta> (the_Var \<langle>x: value\<rangle>\<^sub>v)) = {}"
      using A(2) unfolding defs s_def by auto
    
    have k: "\<Gamma> k = TAtom Value" "fv k = {}" "wf\<^sub>t\<^sub>r\<^sub>m k"
      subgoal using \<delta>(1) wt_subst_trm''[OF \<delta>(2), of "\<langle>x: value\<rangle>\<^sub>v"] by simp
      subgoal using \<delta>(1,4) by blast
      subgoal using \<delta>(1,3) by force
      done
    then obtain fk where fk: "k = Fun fk []"
      using const_type_inv_wf by (cases k) auto

    have fk': "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> \<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t"
      using fk welltyped_constraint_model_deduct_split(2)[OF A(3)] by auto

    have "\<not>welltyped_constraint_model I (A@[\<langle>\<star>, send\<langle>[\<langle>c\<rangle>\<^sub>c]\<rangle>\<rangle>])"
      using subterms_sec(1) A(1) by blast
    hence "\<not>ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> \<langle>c\<rangle>\<^sub>c"
      using A' strand_sem_append_stateful[of "{}" "{}" "unlabel A" "unlabel [\<langle>\<star>, send\<langle>[\<langle>c\<rangle>\<^sub>c]\<rangle>\<rangle>]" I]
      unfolding defs' by auto
    hence "\<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      using fk' deduct_inv'[OF fk'] by force
    moreover have "k \<sqsubseteq> \<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t" by simp
    ultimately have k_in_ik: "k \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I"
      using in_subterms_subset_Union by blast
    hence "k \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<or> (\<exists>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A). k \<sqsubseteq> I x)"
      using const_subterms_subst_cases[of fk I "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"]
      unfolding fk by fast
    hence "fk \<in> \<Union>(funs_term ` ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<or> (\<exists>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. k \<sqsubseteq> I x)"
      unfolding fk by (meson UN_iff funs_term_Fun_subterm' fv_ik\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t )
    hence "fk \<in> \<Union>(funs_term ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<or> (\<exists>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. k \<sqsubseteq> I x)"
      using ik\<^sub>s\<^sub>s\<^sub>t_trms\<^sub>s\<^sub>s\<^sub>t_subset by blast
    moreover have "\<Gamma>\<^sub>v x = TAtom Value" when x: "x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" for x
      using x reachable_constraints_var_types_in_transactions(1)[OF A(1) P(2)]
            P(1) admissible_transaction_Value_vars
      by force
    ultimately have "fk \<in> \<Union>(funs_term ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<or> (\<exists>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<Gamma>\<^sub>v x = TAtom Value \<and> k \<sqsubseteq> I x)"
      by blast
    hence "fk \<in> \<Union>(funs_term ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t A) \<or> (\<exists>x \<in> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A. \<Gamma>\<^sub>v x = TAtom Value \<and> I x = k)"
      using I(1,3) wf_trm_TComp_subterm wf_trm_subst_rangeD
      unfolding fk wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by (metis \<Gamma>.simps(1) term.distinct(1))
    then obtain kn where kn: "fk = Val kn"
      using reachable_constraints_val_funs_private[OF A(1) P(1), of fk]
            constraint_model_Value_term_is_Val[OF A(1) A' P(1)]
            Fun_Value_type_inv[OF k(1)[unfolded fk]]
      unfolding fk is_PubConstValue_def by (cases fk) force+

    obtain \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
      where \<alpha>: "transaction_renaming_subst \<alpha> P A"
      unfolding transaction_renaming_subst_def by blast

    obtain y' yn' where y':
        "\<alpha> (the_Var \<langle>y: value\<rangle>\<^sub>v) = Var y'" "y \<noteq> yn'" "Var y' = \<langle>yn': value\<rangle>\<^sub>v"
      using transaction_renaming_subst_is_renaming(1,2)[OF \<alpha>] by force

    define B where "B \<equiv> A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand Tatt \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>)"
    define J where "J \<equiv> I(y' := k)"

    have "y' \<in> range_vars \<alpha>"
      using y'(1) transaction_renaming_subst_is_renaming(3)[OF \<alpha>]
      by (metis (no_types, lifting) in_mono subst_fv_imgI term.set_intros(3))
    hence y'': "y' \<notin> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      using transaction_renaming_subst_vars_disj(6)[OF \<alpha>] by blast

    have 0: "(k,\<langle>d\<rangle>\<^sub>s) \<notin> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I)"
    proof
      assume a: "(k,\<langle>d\<rangle>\<^sub>s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I)"
      obtain l t t' where t: "(l,insert\<langle>t,t'\<rangle>) \<in> set A" "t \<cdot> I = k" "t' \<cdot> I = \<langle>d\<rangle>\<^sub>s"
        using db\<^sub>s\<^sub>s\<^sub>t_in_cases[OF a[unfolded db\<^sub>s\<^sub>s\<^sub>t_def]] unfolding unlabel_def by auto

      obtain T b B \<alpha> \<sigma> \<xi> where T:
          "prefix (B@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) A"
          "T \<in> set P" "transaction_decl_subst \<xi> T"
          "transaction_fresh_subst \<sigma> T B" "transaction_renaming_subst \<alpha> P B"
          "b \<in> set (transaction_strand T)" "(l, insert\<langle>t,t'\<rangle>) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
          "fst (l, insert\<langle>t,t'\<rangle>) = fst b"
        using reachable_constraints_transaction_action_obtain[OF A(1) t(1)] by metis

      define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

      obtain b' where "b = (l,b')"
        using T(8) by (cases b) simp
      then obtain tb tb'
          where b': "b = (l,insert\<langle>tb,tb'\<rangle>)"
            and tb: "t = tb \<cdot> \<theta>"
            and tb': "t' = tb' \<cdot> \<theta>"
        using T(7) unfolding \<theta>_def by (cases b') auto

      note T_adm = bspec[OF P(1) T(2)]
      note T_wf = admissible_transaction_is_wellformed_transaction(1,3)[OF T_adm]

      have b: "b \<in> set (transaction_updates T)"
        using transaction_strand_memberD[OF T(6)[unfolded b']]
              wellformed_transaction_cases[OF T_wf(1)]
        unfolding b' by blast

      have "\<exists>n. tb = \<langle>n: value\<rangle>\<^sub>v" and *: "tb' = \<langle>d\<rangle>\<^sub>s"
        using tb tb' T(6) t(3) transaction_inserts_are_Value_vars[OF T_wf, of tb tb']
        unfolding b' unlabel_def by (force,force)

      have "is_Insert (snd b)" "the_set_term (snd b) = \<langle>d\<rangle>\<^sub>s" "the_elem_term (snd b) = tb"
        unfolding b' * by simp_all
      hence "transaction_send T \<noteq> []"
            "let (l, a) = hd (transaction_send T)
             in l = \<star> \<and> is_Send a \<and> \<langle>f [\<langle>c\<rangle>\<^sub>c, tb]\<rangle>\<^sub>t \<in> set (the_msgs a)"
        using P_d T(2) b by (fast,fast)
      hence "\<exists>ts. \<langle>\<star>,send\<langle>ts\<rangle>\<rangle> \<in> set (transaction_send T) \<and> \<langle>f [\<langle>c\<rangle>\<^sub>c, tb]\<rangle>\<^sub>t \<in> set ts"
        unfolding is_Send_def by (cases "transaction_send T") auto
      then obtain ts where ts: "\<langle>\<star>,send\<langle>ts\<rangle>\<rangle> \<in> set (transaction_strand T)" "\<langle>f [\<langle>c\<rangle>\<^sub>c, tb]\<rangle>\<^sub>t \<in> set ts"
        unfolding transaction_strand_def by auto
      
      have "\<langle>\<star>,receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>\<rangle> \<in> set A" "\<langle>f [\<langle>c\<rangle>\<^sub>c, t]\<rangle>\<^sub>t \<in> set (ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>)"
        using subst_lsst_memI[OF ts(1), of \<theta>] subst_set_map[OF ts(2), of \<theta>]
              dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(1)[of \<star> "ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>" "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>"]
              set_mono_prefix[OF T(1)[unfolded \<theta>_def[symmetric]]]
        unfolding tb by auto
      hence "\<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t \<in> \<Union>{set ts |ts. \<langle>\<star>, receive\<langle>ts\<rangle>\<rangle> \<in> set (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)}"
        using t(2) subst_lsst_memI[of "\<langle>\<star>,receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>\<rangle>" A I] by force
      thus False
        using A(2) unfolding declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto
    qed

    have "y' \<notin> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
      using y'' fv_ik_subset_vars_sst'[of "unlabel A"] by blast 
    hence 1: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J"
      unfolding J_def by (metis (no_types, lifting) fv_subset image_cong in_mono repl_invariance)

    have "(k,\<langle>d\<rangle>\<^sub>s) \<notin> dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I {}"
      using 0 db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel A" I "[]"]
      unfolding db\<^sub>s\<^sub>s\<^sub>t_def by force
    hence "(k,\<langle>d\<rangle>\<^sub>s) \<notin> dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) J {}"
      using y'' vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel A"]
            db\<^sub>s\<^sub>s\<^sub>t_subst_swap[of "unlabel A" I J "[]"]
            db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel A" _ "[]"]
      unfolding db\<^sub>s\<^sub>s\<^sub>t_def J_def by (metis (no_types, lifting) Un_iff empty_set fun_upd_other)
    hence "((Var y' \<cdot> J, \<langle>d\<rangle>\<^sub>s \<cdot> J) \<notin> dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) J {})"
      unfolding J_def fk by simp
    hence "strand_sem_stateful (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J) (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) J {})
            (unlabel [\<langle>n, \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>\<rangle>]) J"
      using stateful_strand_sem_NegChecks_no_bvars(1)[
              of "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J" "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) J {}" "Var y'" "\<langle>d\<rangle>\<^sub>s" J]
      by simp
    hence 2: "strand_sem_stateful {} {} (unlabel (A@[\<langle>n, \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>\<rangle>])) J"
      using A'' y' y'' vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel A"]
            strand_sem_append_stateful[
              of "{}" "{}" "unlabel A" "unlabel [\<langle>n, \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>\<rangle>]" J]
      unfolding J_def by simp

    have B: "B \<in> reachable_constraints P"
      using reachable_constraints.step[OF A(1) P_Tatt _ _ \<alpha>, of Var Var]
      unfolding B_def Tatt_def transaction_decl_subst_def transaction_fresh_subst_def by simp

    have Tatt': "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand Tatt \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>) =
                  [\<langle>\<star>, send\<langle>[occurs (Var y')]\<rangle>\<rangle>,
                   (l, send\<langle>[\<langle>f [\<langle>c\<rangle>\<^sub>c, Var y']\<rangle>\<^sub>t]\<rangle>),
                   (l', \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>),
                   \<langle>n, receive\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]"
      using y'
      unfolding Tatt_def transaction_strand_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def subst_apply_labeled_stateful_strand_def
      by auto

    have J: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t J" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t J" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range J)"
      unfolding J_def
      subgoal using wt_subst_subst_upd[OF I(1)] k(1) y'(3) by simp 
      subgoal by (metis I(2) k(2) fun_upd_apply interpretation_grounds_all interpretation_substI)
      subgoal using I(3) k(3) by fastforce
      done

    have 3: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J \<turnstile> \<langle>f [\<langle>c\<rangle>\<^sub>c, Var y']\<rangle>\<^sub>t \<cdot> J"
      using 1 fk fk' unfolding J_def by auto

    have 4: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J \<turnstile> occurs (Var y') \<cdot> J"
      using reachable_constraints_occurs_fact_ik_case'[
                OF A(1) P(1) constraint_model_Val_const_in_constr_prefix'[
                              OF A(1) A' P(1) k_in_ik[unfolded fk kn]]]
            intruder_deduct.Axiom[of "occurs k" "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J"]
      unfolding J_def fk kn by fastforce

    have "strand_sem_stateful {} {} (unlabel A) J"
      using 2 strand_sem_append_stateful by force
    hence "strand_sem_stateful {} {}
            (unlabel (A@[\<langle>\<star>, send\<langle>[occurs (Var y')]\<rangle>\<rangle>,
                         \<langle>n, send\<langle>[\<langle>f [\<langle>c\<rangle>\<^sub>c, Var y']\<rangle>\<^sub>t]\<rangle>\<rangle>,
                         \<langle>n, \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>\<rangle>])) J"
      using 2 3 4 strand_sem_append_stateful[of "{}" "{}" _ _ J]
      unfolding unlabel_def ik\<^sub>s\<^sub>s\<^sub>t_def by force
    hence "strand_sem_stateful {} {} (unlabel (B@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])) J"
      using strand_sem_receive_send_append[of "{}" "{}" _ J "attack\<langle>ln n\<rangle>"]
            strand_sem_append_stateful[of "{}" "{}" _ _ J]
      unfolding B_def Tatt' by simp
    hence "welltyped_constraint_model J (B@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
      using B J unfolding defs' by blast
    thus False using B(1) P_sec by blast
  qed
qed

lemma welltyped_leakage_free_short_term_secretI':
  fixes c x y f n d l l' \<tau>
  defines "s \<equiv> \<langle>f [\<langle>c\<rangle>\<^sub>c, Var (TAtom \<tau>,x)]\<rangle>\<^sub>t"
    and "Tatt \<equiv> Transaction (\<lambda>(). []) []
          [(l, receive\<langle>[\<langle>f [\<langle>c\<rangle>\<^sub>c, Var (TAtom \<tau>,y)]\<rangle>\<^sub>t]\<rangle>)]
          [(l', \<langle>Var (TAtom \<tau>,y) not in \<langle>d\<rangle>\<^sub>s\<rangle>)]
          []
          [\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]"
  assumes P:
      "\<forall>T \<in> set P. wellformed_transaction T"
      "\<forall>T \<in> set P. \<forall>x \<in> set (unlabel (transaction_updates T)).
        is_Update x \<longrightarrow> is_Fun (the_set_term x)"
    and subterms_sec:
      "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>. welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>\<star>, send\<langle>[\<langle>c\<rangle>\<^sub>c]\<rangle>\<rangle>])"
    and P_sec:
      "\<forall>\<A> \<in> reachable_constraints P. \<nexists>\<I>\<^sub>\<tau>.
        welltyped_constraint_model \<I>\<^sub>\<tau> (\<A>@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
    and P_Tatt: "Tatt \<in> set P"
    and P_d:
      "\<forall>T \<in> set P. \<forall>a \<in> set (transaction_updates T).
        is_Insert (snd a) \<and> the_set_term (snd a) = \<langle>d\<rangle>\<^sub>s \<longrightarrow>
          transaction_send T \<noteq> [] \<and> (let (l,b) = hd (transaction_send T)
            in l = \<star> \<and> is_Send b \<and> \<langle>f [\<langle>c\<rangle>\<^sub>c, the_elem_term (snd a)]\<rangle>\<^sub>t \<in> set (the_msgs b))"
  shows "welltyped_leakage_free_protocol [s] P"
proof -
  define Q where "Q \<equiv> \<lambda>M t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}"
  define Sec where "Sec \<equiv> {t \<cdot> \<delta> | t \<delta>. Q (set [s]) t \<delta>} - {m. {} \<turnstile>\<^sub>c m}"

  define f' where "f' \<equiv> \<lambda>(T,\<xi>,\<sigma>::('fun,'atom,'sets,'lbl) prot_subst,\<alpha>).
                            dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)"
  define g' where "g' \<equiv> concat \<circ> map f'"

  note defs = Sec_def Q_def
  note defs' = welltyped_constraint_model_def constraint_model_def

  show ?thesis
  proof (rule ccontr)
    assume "\<not>welltyped_leakage_free_protocol [s] P"
    then obtain A I k where A:
        "A \<in> reachable_constraints P" "\<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t \<in> Sec - declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I"
        "welltyped_constraint_model I (A@[\<langle>\<star>, send\<langle>[\<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t]\<rangle>\<rangle>])"
      unfolding welltyped_leakage_free_protocol_def defs s_def by fastforce

    have I: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t I" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range I)"
      using A(3) unfolding defs' by (blast,blast,blast)

    note A' = welltyped_constraint_model_prefix[OF A(3)]

    have "strand_sem_stateful {} {} (unlabel A) I"
      using A' unfolding defs' by simp
    hence A'': "strand_sem_stateful {} {} (unlabel A) (I(z := k))"
      when z: "z \<notin> fv\<^sub>l\<^sub>s\<^sub>s\<^sub>t A" for z
      using z strand_sem_model_swap[of "unlabel A" I "I(z := k)" "{}" "{}"] by auto

    obtain \<delta> where \<delta>:
        "\<delta> (TAtom \<tau>,x) = k" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "fv (\<delta> (TAtom \<tau>,x)) = {}"
      using A(2) unfolding defs s_def by auto
    
    have k: "\<Gamma> k = TAtom \<tau>" "fv k = {}" "wf\<^sub>t\<^sub>r\<^sub>m k"
      subgoal using \<delta>(1) wt_subst_trm''[OF \<delta>(2), of "Var (TAtom \<tau>,x)"] by simp
      subgoal using \<delta>(1,4) by blast
      subgoal using \<delta>(1,3) by force
      done
    then obtain fk where fk: "k = Fun fk []"
      using const_type_inv_wf by (cases k) auto

    have fk': "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I \<turnstile> \<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t"
      using fk welltyped_constraint_model_deduct_split(2)[OF A(3)] by auto

    obtain \<alpha>::"('fun,'atom,'sets,'lbl) prot_subst"
      where \<alpha>: "transaction_renaming_subst \<alpha> P A"
      unfolding transaction_renaming_subst_def by blast

    obtain y' yn' where y': "\<alpha> (TAtom \<tau>,y) = Var y'" "y \<noteq> yn'" "y' = (TAtom \<tau>,yn')"
      using transaction_renaming_subst_is_renaming(1,2)[OF \<alpha>] by force

    define B where "B \<equiv> A@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand Tatt \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>)"
    define J where "J \<equiv> I(y' := k)"

    have "y' \<in> range_vars \<alpha>"
      using y'(1) transaction_renaming_subst_is_renaming(3)[OF \<alpha>]
      by (metis (no_types, lifting) in_mono subst_fv_imgI term.set_intros(3))
    hence y'': "y' \<notin> vars\<^sub>l\<^sub>s\<^sub>s\<^sub>t A"
      using transaction_renaming_subst_vars_disj(6)[OF \<alpha>] by blast

    have 0: "(k,\<langle>d\<rangle>\<^sub>s) \<notin> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I)"
    proof
      assume a: "(k,\<langle>d\<rangle>\<^sub>s) \<in> set (db\<^sub>l\<^sub>s\<^sub>s\<^sub>t A I)"
      obtain l t t' where t: "(l,insert\<langle>t,t'\<rangle>) \<in> set A" "t \<cdot> I = k" "t' \<cdot> I = \<langle>d\<rangle>\<^sub>s"
        using db\<^sub>s\<^sub>s\<^sub>t_in_cases[OF a[unfolded db\<^sub>s\<^sub>s\<^sub>t_def]] unfolding unlabel_def by auto

      obtain T b B \<alpha> \<sigma> \<xi> where T:
          "prefix (B@dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>)) A"
          "T \<in> set P" "transaction_decl_subst \<xi> T"
          "transaction_fresh_subst \<sigma> T B" "transaction_renaming_subst \<alpha> P B"
          "b \<in> set (transaction_strand T)" "(l, insert\<langle>t,t'\<rangle>) = dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p b \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t\<^sub>p \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"
          "fst (l, insert\<langle>t,t'\<rangle>) = fst b"
        using reachable_constraints_transaction_action_obtain[OF A(1) t(1)] by metis

      define \<theta> where "\<theta> \<equiv> \<xi> \<circ>\<^sub>s \<sigma> \<circ>\<^sub>s \<alpha>"

      obtain b' where "b = (l,b')"
        using T(8) by (cases b) simp
      then obtain tb tb'
          where b': "b = (l,insert\<langle>tb,tb'\<rangle>)"
            and tb: "t = tb \<cdot> \<theta>"
            and tb': "t' = tb' \<cdot> \<theta>"
        using T(7) unfolding \<theta>_def by (cases b') auto

      note T_wf = bspec[OF P(1) T(2)] bspec[OF P(2) T(2)]

      have b: "b \<in> set (transaction_updates T)"
        using transaction_strand_memberD[OF T(6)[unfolded b']]
              wellformed_transaction_cases[OF T_wf(1)]
        unfolding b' by blast

      have "is_Fun tb'"
        using bspec[OF P(2) T(2)]
              wellformed_transaction_strand_unlabel_memberD(6)[
                    OF T_wf(1) unlabel_in[OF T(6)[unfolded b']]]
        by fastforce
      hence *: "tb' = \<langle>d\<rangle>\<^sub>s"
        using t(3) unfolding b' tb' by force

      have "is_Insert (snd b)" "the_set_term (snd b) = \<langle>d\<rangle>\<^sub>s" "the_elem_term (snd b) = tb"
        unfolding b' * by simp_all
      hence "transaction_send T \<noteq> []"
            "let (l, a) = hd (transaction_send T)
             in l = \<star> \<and> is_Send a \<and> \<langle>f [\<langle>c\<rangle>\<^sub>c, tb]\<rangle>\<^sub>t \<in> set (the_msgs a)"
        using P_d T(2) b by (fast,fast)
      hence "\<exists>ts. \<langle>\<star>,send\<langle>ts\<rangle>\<rangle> \<in> set (transaction_send T) \<and> \<langle>f [\<langle>c\<rangle>\<^sub>c, tb]\<rangle>\<^sub>t \<in> set ts"
        unfolding is_Send_def by (cases "transaction_send T") auto
      then obtain ts where ts: "\<langle>\<star>,send\<langle>ts\<rangle>\<rangle> \<in> set (transaction_strand T)" "\<langle>f [\<langle>c\<rangle>\<^sub>c, tb]\<rangle>\<^sub>t \<in> set ts"
        unfolding transaction_strand_def by auto
      
      have "\<langle>\<star>,receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>\<rangle> \<in> set A" "\<langle>f [\<langle>c\<rangle>\<^sub>c, t]\<rangle>\<^sub>t \<in> set (ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>)"
        using subst_lsst_memI[OF ts(1), of \<theta>] subst_set_map[OF ts(2), of \<theta>]
              dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_steps_iff(1)[of \<star> "ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>" "transaction_strand T \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<theta>"]
              set_mono_prefix[OF T(1)[unfolded \<theta>_def[symmetric]]]
        unfolding tb by auto
      hence "\<langle>f [\<langle>c\<rangle>\<^sub>c, k]\<rangle>\<^sub>t \<in> \<Union>{set ts |ts. \<langle>\<star>, receive\<langle>ts\<rangle>\<rangle> \<in> set (A \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t I)}"
        using t(2) subst_lsst_memI[of "\<langle>\<star>,receive\<langle>ts \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta>\<rangle>\<rangle>" A I] by force
      thus False
        using A(2) unfolding declassified\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def by auto
    qed

    have "y' \<notin> fv\<^sub>s\<^sub>e\<^sub>t (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A)"
      using y'' fv_ik_subset_vars_sst'[of "unlabel A"] by blast 
    hence 1: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I = ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J"
      unfolding J_def by (metis (no_types, lifting) fv_subset image_cong in_mono repl_invariance)

    have "(k,\<langle>d\<rangle>\<^sub>s) \<notin> dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) I {}"
      using 0 db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel A" I "[]"]
      unfolding db\<^sub>s\<^sub>s\<^sub>t_def by force
    hence "(k,\<langle>d\<rangle>\<^sub>s) \<notin> dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) J {}"
      using y'' vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel A"]
            db\<^sub>s\<^sub>s\<^sub>t_subst_swap[of "unlabel A" I J "[]"]
            db\<^sub>s\<^sub>s\<^sub>t_set_is_dbupd\<^sub>s\<^sub>s\<^sub>t[of "unlabel A" _ "[]"]
      unfolding db\<^sub>s\<^sub>s\<^sub>t_def J_def by (metis (no_types, lifting) Un_iff empty_set fun_upd_other)
    hence "((Var y' \<cdot> J, \<langle>d\<rangle>\<^sub>s \<cdot> J) \<notin> dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) J {})"
      unfolding J_def fk by simp
    hence "strand_sem_stateful (ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J) (dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) J {})
            (unlabel [\<langle>n, \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>\<rangle>]) J"
      using stateful_strand_sem_NegChecks_no_bvars(1)[
              of "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J" "dbupd\<^sub>s\<^sub>s\<^sub>t (unlabel A) J {}" "Var y'" "\<langle>d\<rangle>\<^sub>s" J]
      by simp
    hence 2: "strand_sem_stateful {} {} (unlabel (A@[\<langle>n, \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>\<rangle>])) J"
      using A'' y' y'' vars\<^sub>s\<^sub>s\<^sub>t_is_fv\<^sub>s\<^sub>s\<^sub>t_bvars\<^sub>s\<^sub>s\<^sub>t[of "unlabel A"]
            strand_sem_append_stateful[
              of "{}" "{}" "unlabel A" "unlabel [\<langle>n, \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>\<rangle>]" J]
      unfolding J_def by simp

    have B: "B \<in> reachable_constraints P"
      using reachable_constraints.step[OF A(1) P_Tatt _ _ \<alpha>, of Var Var]
      unfolding B_def Tatt_def transaction_decl_subst_def transaction_fresh_subst_def by simp

    have Tatt': "dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_strand Tatt \<cdot>\<^sub>l\<^sub>s\<^sub>s\<^sub>t \<alpha>) =
                  [(l, send\<langle>[\<langle>f [\<langle>c\<rangle>\<^sub>c, Var y']\<rangle>\<^sub>t]\<rangle>),
                   (l', \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>),
                   \<langle>n, receive\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]"
      using y'
      unfolding Tatt_def transaction_strand_def dual\<^sub>l\<^sub>s\<^sub>s\<^sub>t_def subst_apply_labeled_stateful_strand_def
      by auto

    have J: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t J" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t J" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range J)"
      unfolding J_def
      subgoal using wt_subst_subst_upd[OF I(1)] k(1) y'(3) by simp 
      subgoal by (metis I(2) k(2) fun_upd_apply interpretation_grounds_all interpretation_substI)
      subgoal using I(3) k(3) by fastforce
      done

    have 3: "ik\<^sub>l\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t J \<turnstile> \<langle>f [\<langle>c\<rangle>\<^sub>c, Var y']\<rangle>\<^sub>t \<cdot> J"
      using 1 fk fk' unfolding J_def by auto

    have "strand_sem_stateful {} {} (unlabel A) J"
      using 2 strand_sem_append_stateful by force
    hence "strand_sem_stateful {} {}
            (unlabel (A@[\<langle>n, send\<langle>[\<langle>f [\<langle>c\<rangle>\<^sub>c, Var y']\<rangle>\<^sub>t]\<rangle>\<rangle>,
                         \<langle>n, \<langle>Var y' not in \<langle>d\<rangle>\<^sub>s\<rangle>\<rangle>])) J"
      using 2 3 strand_sem_append_stateful[of "{}" "{}" _ _ J]
      unfolding unlabel_def ik\<^sub>s\<^sub>s\<^sub>t_def by force
    hence "strand_sem_stateful {} {} (unlabel (B@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])) J"
      using strand_sem_receive_send_append[of "{}" "{}" _ J "attack\<langle>ln n\<rangle>"]
            strand_sem_append_stateful[of "{}" "{}" _ _ J]
      unfolding B_def Tatt' by simp
    hence "welltyped_constraint_model J (B@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
      using B J unfolding defs' by blast
    thus False using B(1) P_sec by blast
  qed
qed

definition welltyped_leakage_free_invkey_conditions' where
  "welltyped_leakage_free_invkey_conditions' invfun privfunsec declassifiedset S n P \<equiv>
    let f = \<lambda>s. is_Var s \<and> fst (the_Var s) = TAtom Value;
        g = \<lambda>s. is_Fun s \<and> args s = [] \<and> is_Set (the_Fun s) \<and>
                arity\<^sub>s (the_Set (the_Fun s)) = 0;
        h = \<lambda>s. is_Fun s \<and> args s = [] \<and> is_Fu (the_Fun s) \<and>
                public\<^sub>f (the_Fu (the_Fun s)) \<and> arity\<^sub>f (the_Fu (the_Fun s)) = 0
    in (\<forall>s\<in>set S.
          f s \<or>
          (is_Fun s \<and> the_Fun s = Pair \<and> length (args s) = 2 \<and> g (args s ! 1)) \<or>
          g s \<or> h s \<or> s = \<langle>privfunsec\<rangle>\<^sub>c \<or> s = Fun OccursSec [] \<or>
          (is_Fun s \<and> the_Fun s = OccursFact \<and> length (args s) = 2 \<and>
           args s ! 0 = Fun OccursSec []) \<or>
          (is_Fun s \<and> the_Fun s = Fu invfun \<and> length (args s) = 2 \<and>
           args s ! 0 = \<langle>privfunsec\<rangle>\<^sub>c \<and> f (args s ! 1)) \<or>
          (is_Fun s \<and> is_Fu (the_Fun s) \<and> fv s = {} \<and>
           Transaction (\<lambda>(). []) [] [\<langle>n, receive\<langle>[s]\<rangle>\<rangle>] [] [] [\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]\<in>set P)) \<and>
       (\<not>public\<^sub>f privfunsec \<and> arity\<^sub>f privfunsec = 0 \<and> \<Gamma>\<^sub>f privfunsec \<noteq> None) \<and>
       (\<forall>T\<in>set P. transaction_fresh T \<noteq> [] \<longrightarrow>
         transaction_send T \<noteq> [] \<and>
         (let (l, a) = hd (transaction_send T)
          in l = \<star> \<and> is_Send a \<and> Var ` set (transaction_fresh T) \<subseteq> set (the_msgs a))) \<and>
       (\<forall>T\<in>set P. \<forall>x\<in>vars_transaction T. is_Var (\<Gamma>\<^sub>v x)) \<and>
       (\<forall>T\<in>set P. \<forall>x\<in>set (transaction_fresh T). \<Gamma>\<^sub>v x = Var Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)) \<and>
       (\<forall>T\<in>set P. \<forall>f\<in>\<Union>(funs_term ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). \<not>is_Set f) \<and>
       (\<forall>T\<in>set P. \<forall>r\<in>set (transaction_send T).
          OccursFact \<in> \<Union>(funs_term ` trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd r)) \<longrightarrow> has_LabelS r) \<and>
       (\<forall>T\<in>set P. \<forall>t\<in>subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)).
          \<langle>privfunsec\<rangle>\<^sub>c \<notin> set (snd (Ana t))) \<and>
       (\<forall>T\<in>set P. \<langle>privfunsec\<rangle>\<^sub>c \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<and>
       (\<forall>T\<in>set P. \<forall>a\<in>set (transaction_updates T).
            is_Insert (snd a) \<and> the_set_term (snd a) = \<langle>declassifiedset\<rangle>\<^sub>s \<longrightarrow>
              transaction_send T \<noteq> [] \<and>
              (let (l, b) = hd (transaction_send T)
               in l = \<star> \<and> is_Send b \<and>
                  \<langle>invfun [\<langle>privfunsec\<rangle>\<^sub>c, the_elem_term (snd a)]\<rangle>\<^sub>t \<in> set (the_msgs b)))"

definition welltyped_leakage_free_invkey_conditions where
  "welltyped_leakage_free_invkey_conditions invfun privfunsec declassifiedset S n P \<equiv>
    let Tatt = \<lambda>R. Transaction (\<lambda>(). []) []
                    (R@[\<langle>n, receive\<langle>[\<langle>invfun [\<langle>privfunsec\<rangle>\<^sub>c, \<langle>0: value\<rangle>\<^sub>v]\<rangle>\<^sub>t]\<rangle>\<rangle>])
                    [\<langle>\<star>, \<langle>\<langle>0: value\<rangle>\<^sub>v not in \<langle>declassifiedset\<rangle>\<^sub>s\<rangle>\<rangle>]
                    []
                    [\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]
    in welltyped_leakage_free_invkey_conditions' invfun privfunsec declassifiedset S n P \<and>
       (if Tatt [\<langle>\<star>, receive\<langle>[occurs \<langle>0: value\<rangle>\<^sub>v]\<rangle>\<rangle>] \<in> set P
        then \<forall>T\<in>set P. admissible_transaction T
        else Tatt [] \<in> set P \<and>
             (\<forall>T\<in>set P. wellformed_transaction T) \<and>
             (\<forall>T\<in>set P. admissible_transaction_terms T) \<and>
             (\<forall>T\<in>set P. bvars_transaction T = {}) \<and>
             (\<forall>T\<in>set P. transaction_decl T () = []) \<and>
             (\<forall>T\<in>set P. \<forall>x\<in>set (transaction_fresh T). let \<tau> = fst x
                in \<tau> = TAtom Value \<and> \<tau> \<noteq> \<Gamma> \<langle>privfunsec\<rangle>\<^sub>c) \<and>
             (\<forall>T\<in>set P. \<forall>x\<in>vars_transaction T. let \<tau> = fst x
                in is_Var \<tau> \<and> (the_Var \<tau> = Value \<or> is_Atom (the_Var \<tau>)) \<and> \<tau> \<noteq> \<Gamma> \<langle>privfunsec\<rangle>\<^sub>c) \<and>
             (\<forall>T\<in>set P. \<forall>t\<in>subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)).
                Fun OccursSec [] \<notin> set (snd (Ana t))) \<and>
             (\<forall>T\<in>set P. Fun OccursSec [] \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)) \<and>
             (\<forall>T\<in>set P. \<forall>x\<in>set (unlabel (transaction_updates T)).
                is_Update x \<longrightarrow> is_Fun (the_set_term x)) \<and>
             (\<forall>s\<in>set S. is_Fun s \<longrightarrow> the_Fun s \<noteq> OccursFact))"

lemma welltyped_leakage_free_invkeyI:
  assumes P_wt_secure: "\<forall>\<A> \<in> reachable_constraints P.
                         \<nexists>\<I>. welltyped_constraint_model \<I> (\<A>@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
    and a: "welltyped_leakage_free_invkey_conditions invfun privsec declassset S n P"
  shows "welltyped_leakage_free_protocol S P"
proof -
  let ?Tatt' = "\<lambda>R C. Transaction (\<lambda>(). []) [] R C [] [\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>]
                        ::('fun,'atom,'sets,'lbl) prot_transaction"
  let ?Tatt = "\<lambda>R. ?Tatt' (R@[\<langle>n, receive\<langle>[\<langle>invfun [\<langle>privsec\<rangle>\<^sub>c, \<langle>0: value\<rangle>\<^sub>v]\<rangle>\<^sub>t]\<rangle>\<rangle>])
                          [\<langle>\<star>, \<langle>\<langle>0: value\<rangle>\<^sub>v not in \<langle>declassset\<rangle>\<^sub>s\<rangle>\<rangle>]"
  
  define Tatt1 where "Tatt1 \<equiv> ?Tatt [\<langle>\<star>, receive\<langle>[occurs \<langle>0: value\<rangle>\<^sub>v]\<rangle>\<rangle>]"
  define Tatt2 where "Tatt2 \<equiv> ?Tatt []"
  define Tatt_lts where "Tatt_lts \<equiv> \<lambda>s. ?Tatt' [\<langle>n, receive\<langle>[s]\<rangle>\<rangle>] []"

  note defs = welltyped_leakage_free_invkey_conditions_def Let_def

  note defs' = defs welltyped_leakage_free_invkey_conditions'_def

  note Tatts = Tatt1_def Tatt2_def Tatt_lts_def

  obtain at where 0: "\<not>public\<^sub>f privsec" "arity\<^sub>f privsec = 0" "\<Gamma>\<^sub>f privsec = Some at"
    using a unfolding defs' by fast

  have *: "\<forall>T\<in>set P. admissible_transaction T" when "Tatt1 \<in> set P"
    using a that unfolding defs Tatts by meson

  have **: "Tatt1 \<in> set P \<or> Tatt2 \<in> set P" using a unfolding defs Tatts by argo

  have ***:
    "\<forall>T\<in>set P. \<forall>x\<in>set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<and> \<Gamma>\<^sub>v x \<noteq> \<Gamma> \<langle>privsec\<rangle>\<^sub>c"
    "\<forall>T\<in>set P. \<forall>x\<in>vars_transaction T. \<exists>a. \<Gamma>\<^sub>v x = TAtom a \<and>
          (a = Value \<or> (\<exists>b. a = Atom b)) \<and> TAtom a \<noteq> \<Gamma> \<langle>privsec\<rangle>\<^sub>c"
    when "Tatt1 \<notin> set P"
    subgoal using a that \<Gamma>\<^sub>v_TAtom''(2) unfolding defs Tatts by metis
    subgoal
      using a that \<Gamma>\<^sub>v_TAtom''(1,2)
      unfolding defs Tatts[symmetric] is_Atom_def is_Var_def by fastforce
    done

  have ****: "s \<noteq> occurs x"
    when "Tatt1 \<notin> set P" "s \<in> set S" for s x
    using a that ** unfolding defs Tatts the_Fun_def by fastforce

  have 1:
      "\<forall>T\<in>set P. transaction_fresh T \<noteq> [] \<longrightarrow>
        transaction_send T \<noteq> [] \<and>
        (let (l, a) = hd (transaction_send T)
         in l = \<star> \<and> is_Send a \<and> Var ` set (transaction_fresh T) \<subseteq> set (the_msgs a))"
      "\<forall>T\<in>set P. \<forall>x\<in>vars_transaction T. is_Var (\<Gamma>\<^sub>v x)"
      "\<forall>T\<in>set P. \<forall>x\<in>set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
      "\<forall>T\<in>set P. \<forall>f\<in>\<Union>(funs_term ` trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). \<not>is_Set f"
      "\<forall>T\<in>set P. \<forall>r\<in>set (transaction_send T).
        OccursFact \<in> \<Union>(funs_term ` trms\<^sub>s\<^sub>s\<^sub>t\<^sub>p (snd r)) \<longrightarrow> has_LabelS r"
      "\<forall>T\<in>set P. \<forall>t\<in>subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). \<langle>privsec\<rangle>\<^sub>c \<notin> set (snd (Ana t))"
      "\<forall>T\<in>set P. \<langle>privsec\<rangle>\<^sub>c \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
      "\<forall>T\<in>set P. \<forall>a\<in>set (transaction_updates T).
        is_Insert (snd a) \<and> the_set_term (snd a) = \<langle>declassset\<rangle>\<^sub>s \<longrightarrow>
        transaction_send T \<noteq> [] \<and>
        (let (l, b) = hd (transaction_send T)
         in l = \<star> \<and> is_Send b \<and>
            \<langle>invfun [\<langle>privsec\<rangle>\<^sub>c, the_elem_term (snd a)]\<rangle>\<^sub>t \<in> set (the_msgs b))"
    using a unfolding defs' by (meson,meson,meson,meson,meson,meson,meson,meson)

  have 2:
      "\<forall>T\<in>set P. wellformed_transaction T"
      "\<forall>T\<in>set P. \<forall>x\<in>vars_transaction T \<union> set (transaction_fresh T). \<Gamma> \<langle>privsec\<rangle>\<^sub>c \<noteq> \<Gamma>\<^sub>v x"
      "\<forall>T\<in>set P. admissible_transaction_terms T"
      "\<forall>T\<in>set P. \<forall>x\<in>set (transaction_fresh T). \<Gamma>\<^sub>v x = TAtom Value"
      "\<forall>T\<in>set P. transaction_decl T () = []"
      "\<forall>T\<in>set P. \<forall>x\<in>vars_transaction T. \<Gamma>\<^sub>v x = TAtom Value \<or> (\<exists>a. \<Gamma>\<^sub>v x = \<langle>a\<rangle>\<^sub>\<tau>\<^sub>a)"
      "\<forall>T\<in>set P. \<forall>x\<in>vars_transaction T \<union> set (transaction_fresh T). \<Gamma>\<^sub>v x \<noteq> TAtom SetType"
      "\<forall>T\<in>set P. \<forall>x\<in>vars_transaction T \<union> set (transaction_fresh T). \<Gamma>\<^sub>v x \<noteq> TAtom OccursSecType"
      "\<forall>T\<in>set P. \<forall>t\<in>subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)). Fun OccursSec [] \<notin> set (snd (Ana t))"
      "\<forall>T\<in>set P. Fun OccursSec [] \<notin> trms\<^sub>l\<^sub>s\<^sub>s\<^sub>t (transaction_send T)"
      "\<forall>T\<in>set P. bvars_transaction T = {}"
      "\<forall>T\<in>set P. \<forall>x\<in>set (unlabel (transaction_updates T)). is_Update x \<longrightarrow> is_Fun (the_set_term x)"
    subgoal using a * unfolding defs by (metis admissible_transaction_is_wellformed_transaction(1))
    subgoal
      apply (cases "Tatt1 \<in> set P")
      subgoal using a * admissible_transactionE(2,3) \<Gamma>_Fu_simps(4) unfolding defs Tatts by force
      subgoal using a \<Gamma>_Fu_simps(4) unfolding defs Tatts by fastforce
      done
    subgoal using a * admissible_transaction_is_wellformed_transaction(4) unfolding defs by metis
    subgoal using a * admissible_transactionE(2) unfolding defs Tatts[symmetric] by fastforce
    subgoal using a * admissible_transactionE(1) unfolding defs Tatts[symmetric] by metis
    subgoal using * *** admissible_transactionE(3) by fast
    subgoal using * *** admissible_transactionE(2,3) by (cases "Tatt1 \<in> set P") (force, fastforce)
    subgoal using * *** admissible_transactionE(2,3) by (cases "Tatt1 \<in> set P") (force, fastforce)
    subgoal
      using a * admissible_transaction_is_wellformed_transaction(5)
            admissible_transaction_occurs_checksE6
      unfolding defs by metis
    subgoal
      using a * admissible_transaction_is_wellformed_transaction(5)
            admissible_transaction_occurs_checksE5
      unfolding defs by metis
    subgoal
      using a * admissible_transaction_no_bvars(2)
      unfolding defs Tatts[symmetric] by fastforce
    subgoal
      using a * admissible_transaction_is_wellformed_transaction(3)
      unfolding defs Tatts[symmetric] admissible_transaction_updates_def by fastforce
    done

  have Tatt_lts_case:
      "\<exists>\<theta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> inj_on \<theta> (fv s) \<and> \<theta> ` fv s \<subseteq> range Var \<and>
           ?Tatt' [\<langle>n, receive\<langle>[s \<cdot> \<theta>]\<rangle>\<rangle>] [] \<in> set P"
    when s: "fv s = {}" "Tatt_lts s \<in> set P" for s
  proof -
    have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var" "inj_on Var (fv s)" "Var ` fv s \<subseteq> range Var" "s \<cdot> Var = s"
      using s(1) by simp_all
    thus ?thesis using s(2) unfolding Tatts by metis
  qed

  have Tatt1_case:
      "?Tatt' [\<langle>\<star>, receive\<langle>[occurs \<langle>0: value\<rangle>\<^sub>v]\<rangle>\<rangle>, \<langle>n, receive\<langle>[\<langle>invfun [\<langle>privsec\<rangle>\<^sub>c, \<langle>0: value\<rangle>\<^sub>v]\<rangle>\<^sub>t]\<rangle>\<rangle>] 
              [\<langle>\<star>, \<langle>\<langle>0: value\<rangle>\<^sub>v not in \<langle>declassset\<rangle>\<^sub>s\<rangle>\<rangle>] \<in> set P"
      when "Tatt1 \<in> set P"
    using that unfolding Tatts by auto

  have Tatt2_case:
      "?Tatt' [\<langle>n, receive\<langle>[\<langle>invfun [\<langle>privsec\<rangle>\<^sub>c, \<langle>0: value\<rangle>\<^sub>v]\<rangle>\<^sub>t]\<rangle>\<rangle>] 
              [\<langle>\<star>, \<langle>\<langle>0: value\<rangle>\<^sub>v not in \<langle>declassset\<rangle>\<^sub>s\<rangle>\<rangle>] \<in> set P"
    when "Tatt2 \<in> set P"
    using that unfolding Tatts by auto

  note 3 = pair_def case_prod_conv
  note 4 = welltyped_leakage_free_priv_constI'[OF 0(1-3) 2(1,2) 1(2,3,6,7)]
  note 5 = welltyped_leakage_free_setop_pairI[OF 2(1,6) 1(4) 2(4,5,3), unfolded 3]
           welltyped_leakage_free_set_constI(2)[OF 2(1) 1(4) 2(7) 1(2,3), unfolded 3]
           welltyped_leakage_free_pub_constI
           4(2)
           welltyped_leakage_free_occurssec_constI(2)[OF 2(1,8-10) 1(2,3)]
           welltyped_leakage_free_value_constI[OF 2(1,3,5,11) 1(1)]
           welltyped_leakage_free_short_term_secretI'[
             OF 2(1,12) 4(1) P_wt_secure Tatt2_case 1(8)]

           welltyped_leakage_free_long_term_secretI[OF P_wt_secure Tatt_lts_case]

           welltyped_leakage_free_short_term_secretI[
             OF * 1(3) 4(1) P_wt_secure Tatt1_case 1(8)]
           welltyped_leakage_free_occurs_factI[OF * 1(5)]

           ** ****

  have 6: "is_Fun s \<and> length (args s) = 2 \<longleftrightarrow> (\<exists>f t u. s = Fun f [t, u])"
    for s::"('fun,'atom,'sets,'lbl) prot_term"
    by auto

  define pubconst_cond where
    "pubconst_cond \<equiv> \<lambda>s::('fun,'atom,'sets,'lbl) prot_term.
      is_Fun s \<and> args s = [] \<and> is_Fu (the_Fun s) \<and>
      public\<^sub>f (the_Fu (the_Fun s)) \<and> arity\<^sub>f (the_Fu (the_Fun s)) = 0"

  define valuevar_cond where
    "valuevar_cond \<equiv> \<lambda>s::('fun,'atom,'sets,'lbl) prot_term.
      is_Var s \<and> fst (the_Var s) = TAtom Value"

  define setconst_cond where
    "setconst_cond \<equiv> \<lambda>s::('fun,'atom,'sets,'lbl) prot_term.
      is_Fun s \<and> args s = [] \<and> is_Set (the_Fun s) \<and> arity\<^sub>s (the_Set (the_Fun s)) = 0"

  define setop_pair_cond where
    "setop_pair_cond \<equiv> \<lambda>s. 
      is_Fun s \<and> the_Fun s = Pair \<and> length (args s) = 2 \<and> setconst_cond (args s ! 1)"

  define occursfact_cond where
    "occursfact_cond \<equiv> \<lambda>s::('fun,'atom,'sets,'lbl) prot_term.
      is_Fun s \<and> the_Fun s = OccursFact \<and> length (args s) = 2 \<and>
      args s ! 0 = Fun OccursSec []"

  define invkey_cond where
    "invkey_cond \<equiv> \<lambda>s.
      is_Fun s \<and> the_Fun s = Fu invfun \<and> length (args s) = 2 \<and>
      args s ! 0 = \<langle>privsec\<rangle>\<^sub>c \<and> valuevar_cond (args s ! 1)"

  define ground_lts_cond where
    "ground_lts_cond \<equiv> \<lambda>s. is_Fun s \<and> is_Fu (the_Fun s) \<and> fv s = {} \<and> Tatt_lts s \<in> set P"

  note cond_defs =
    pubconst_cond_def valuevar_cond_def setconst_cond_def setop_pair_cond_def
    occursfact_cond_def invkey_cond_def ground_lts_cond_def

  have "(\<exists>m. s = \<langle>m: value\<rangle>\<^sub>v) \<longleftrightarrow> valuevar_cond s"
       "(\<exists>x c. arity\<^sub>s c = 0 \<and> s = Fun Pair [x, \<langle>c\<rangle>\<^sub>s]) \<longleftrightarrow> setop_pair_cond s"
       "(\<exists>c. arity\<^sub>s c = 0 \<and> s = \<langle>c\<rangle>\<^sub>s) \<longleftrightarrow> setconst_cond s"
       "(\<exists>c. public\<^sub>f c \<and> arity\<^sub>f c = 0 \<and> s = \<langle>c\<rangle>\<^sub>c) \<longleftrightarrow> pubconst_cond s"
       "(\<exists>x. s = occurs x) \<longleftrightarrow> occursfact_cond s"
       "(\<exists>x. s = \<langle>invfun [\<langle>privsec\<rangle>\<^sub>c, \<langle>x: value\<rangle>\<^sub>v]\<rangle>\<^sub>t) \<longleftrightarrow> invkey_cond s"
       "(\<exists>f ts. s = \<langle>f ts\<rangle>\<^sub>t \<and> fv s = {} \<and> Tatt_lts s \<in> set P) \<longleftrightarrow> ground_lts_cond s"
    for s::"('fun,'atom,'sets,'lbl) prot_term"
    unfolding is_Set_def the_Set_def is_Fu_def cond_defs
    by (fastforce,use 6[of s] in fastforce,fastforce,force,fastforce,fastforce,fastforce)
  moreover have
      "(\<forall>s \<in> set S. valuevar_cond s \<or> setop_pair_cond s \<or> setconst_cond s \<or> pubconst_cond s \<or>
                    s = \<langle>privsec\<rangle>\<^sub>c \<or> s = Fun OccursSec [] \<or> occursfact_cond s \<or> invkey_cond s \<or>
                    ground_lts_cond s) \<and>
       (\<not>public\<^sub>f privsec \<and> arity\<^sub>f privsec = 0 \<and> \<Gamma>\<^sub>f privsec \<noteq> None)"
    using a unfolding defs' cond_defs Tatts by meson
  ultimately have 7:
      "\<forall>s \<in> set S.
        (\<exists>x c. arity\<^sub>s c = 0 \<and> s = Fun Pair [x, \<langle>c\<rangle>\<^sub>s]) \<or>
        (\<exists>c. arity\<^sub>s c = 0 \<and> s = \<langle>c\<rangle>\<^sub>s) \<or>
        (\<exists>c. public\<^sub>f c \<and> arity\<^sub>f c = 0 \<and> s = \<langle>c\<rangle>\<^sub>c) \<or>
        s = \<langle>privsec\<rangle>\<^sub>c \<or> s = Fun OccursSec [] \<or>
        (\<exists>m. s = \<langle>m: value\<rangle>\<^sub>v) \<or>
        (\<exists>x. s = occurs x) \<or>
        (\<exists>x. s = \<langle>invfun [\<langle>privsec\<rangle>\<^sub>c, \<langle>x: value\<rangle>\<^sub>v]\<rangle>\<^sub>t) \<or>
        (\<exists>f ts. s = \<langle>f ts\<rangle>\<^sub>t \<and> fv s = {} \<and> Tatt_lts s \<in> set P)"
    unfolding Let_def by fastforce

  show ?thesis
    by (rule iffD2[OF welltyped_leakage_free_protocol_pointwise]; unfold list_all_iff; intro ballI)
       (use bspec[OF 7] 5 in blast)
qed

end

end

locale composable_stateful_protocols =
  pm: stateful_protocol_model arity\<^sub>f arity\<^sub>s public\<^sub>f Ana\<^sub>f \<Gamma>\<^sub>f label_witness1 label_witness2
  for arity\<^sub>f::"'fun \<Rightarrow> nat"
    and arity\<^sub>s::"'sets \<Rightarrow> nat"
    and public\<^sub>f::"'fun \<Rightarrow> bool"
    and Ana\<^sub>f::"'fun \<Rightarrow> ((('fun,'atom::finite,'sets,nat) prot_fun, nat) term list \<times> nat list)"
    and \<Gamma>\<^sub>f::"'fun \<Rightarrow> 'atom option"
    and label_witness1::"nat"
    and label_witness2::"nat"
  +
  fixes Pc::"('fun,'atom,'sets,nat) prot_transaction list"
    and Ps Ps_with_star_projs::"('fun,'atom,'sets,nat) prot_transaction list list"
    and Pc_SMP Sec_symbolic::"('fun,'atom,'sets,nat) prot_term list"
    and Ps_GSMPs::"(nat \<times> ('fun,'atom,'sets,nat) prot_term list) list"
  assumes Pc_def: "Pc = concat Ps"
    and Ps_with_star_projs_def: "let Pc' = Pc; L = [0..<length Ps] in
          Ps_with_star_projs = map (\<lambda>n. (map (transaction_proj n) Pc')) L \<and>
          set L = set (remdups (concat (
                          map (\<lambda>T. map (the_LabelN \<circ> fst)
                                       (filter (Not \<circ> has_LabelS) (transaction_strand T)))
                              Pc')))"
    and Pc_wellformed_composable:
          "list_all (list_all (Not \<circ> has_LabelS) \<circ> tl \<circ> transaction_send) Pc"
          "pm.wellformed_composable_protocols Ps Pc_SMP"
          "pm.composable_protocols Ps Ps_GSMPs Sec_symbolic"
begin

theorem composed_protocol_preserves_component_goals:
  assumes components_leakage_free:
      "list_all (pm.welltyped_leakage_free_protocol Sec_symbolic) Ps_with_star_projs"
    and n_def: "n < length Ps_with_star_projs"
    and P_def: "P = Ps_with_star_projs ! n"
    and P_welltyped_secure:
      "\<forall>\<A> \<in> pm.reachable_constraints P. \<nexists>\<I>.
          pm.welltyped_constraint_model \<I> (\<A>@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
  shows "\<forall>\<A> \<in> pm.reachable_constraints Pc. \<nexists>\<I>.
          pm.constraint_model \<I> (\<A>@[\<langle>n, send\<langle>[attack\<langle>ln n\<rangle>]\<rangle>\<rangle>])"
proof -
  note 0 = Ps_with_star_projs_def[unfolded Let_def]

  have 1:
      "set Ps_with_star_projs =
          (\<lambda>n. map (transaction_proj n) Pc) `
            set (remdups (concat (map (\<lambda>T. map (the_LabelN \<circ> fst)
                                               (filter (Not \<circ> has_LabelS) (transaction_strand T)))
                                      Pc)))"
    by (metis (mono_tags, lifting) 0 image_set)

  have 2: "Ps_with_star_projs ! n = map (transaction_proj n) Pc"
    using conjunct1[OF 0] n_def by fastforce

  show ?thesis
    by (rule pm.composable_protocols_par_comp_prot'[
                  OF Pc_def 1 Pc_wellformed_composable
                     components_leakage_free 2 P_welltyped_secure[unfolded P_def]])
qed

end

end
