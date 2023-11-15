section \<open>Consistency\<close>

theory Consistency
  imports
    Soundness
begin

definition is_inconsistent_set :: "form set \<Rightarrow> bool" where
  [iff]: "is_inconsistent_set \<G> \<longleftrightarrow> \<G> \<turnstile> F\<^bsub>o\<^esub>"

definition \<Q>\<^sub>0_is_inconsistent :: bool where
  [iff]: "\<Q>\<^sub>0_is_inconsistent \<longleftrightarrow> \<turnstile> F\<^bsub>o\<^esub>"

definition is_wffo_consistent_with :: "form \<Rightarrow> form set \<Rightarrow> bool" where
  [iff]: "is_wffo_consistent_with B \<G> \<longleftrightarrow> \<not> is_inconsistent_set (\<G> \<union> {B})"

subsection \<open>Existence of a standard model\<close>

text \<open>We construct a standard model in which \<open>\<D> i\<close> is the set \<open>{0}\<close>:\<close>

primrec singleton_standard_domain_family ("\<D>\<^sup>S") where
  "\<D>\<^sup>S i = 1" \<comment> \<open>i.e., \<^term>\<open>\<D>\<^sup>S i = set {0}\<close>\<close>
| "\<D>\<^sup>S o = \<bool>"
| "\<D>\<^sup>S (\<alpha>\<rightarrow>\<beta>) = \<D>\<^sup>S \<alpha> \<longmapsto> \<D>\<^sup>S \<beta>"

interpretation singleton_standard_frame: frame "\<D>\<^sup>S"
proof unfold_locales
  {
    fix \<alpha>
    have "\<D>\<^sup>S \<alpha> \<noteq> 0"
    proof (induction \<alpha>)
      case (TFun \<beta> \<gamma>)
      from \<open>\<D>\<^sup>S \<gamma> \<noteq> 0\<close> obtain y where "y \<in> elts (\<D>\<^sup>S \<gamma>)"
        by fastforce
      then have "(\<^bold>\<lambda>z \<^bold>: \<D>\<^sup>S \<beta>\<^bold>. y) \<in> elts (\<D>\<^sup>S \<beta> \<longmapsto> \<D>\<^sup>S \<gamma>)"
        by (intro VPi_I)
      then show ?case
        by force
    qed simp_all
  }
  then show "\<forall>\<alpha>. \<D>\<^sup>S \<alpha> \<noteq> 0"
    by (intro allI)
qed simp_all

definition singleton_standard_constant_denotation_function ("\<J>\<^sup>S") where
  [simp]: "\<J>\<^sup>S k =
    (
      if
        \<exists>\<beta>. is_Q_constant_of_type k \<beta>
      then
        let \<beta> = type_of_Q_constant k in q\<^bsub>\<beta>\<^esub>\<^bsup>\<D>\<^sup>S\<^esup>
      else
      if
        is_iota_constant k
      then
        \<^bold>\<lambda>z \<^bold>: \<D>\<^sup>S (i\<rightarrow>o)\<^bold>. 0
      else
        case k of (c, \<alpha>) \<Rightarrow> SOME z. z \<in> elts (\<D>\<^sup>S \<alpha>)
    )"

interpretation singleton_standard_premodel: premodel "\<D>\<^sup>S" "\<J>\<^sup>S"
proof (unfold_locales)
  show "\<forall>\<alpha>. \<J>\<^sup>S (Q_constant_of_type \<alpha>) = q\<^bsub>\<alpha>\<^esub>\<^bsup>\<D>\<^sup>S\<^esup>"
    by simp
next
  show "singleton_standard_frame.is_unique_member_selector (\<J>\<^sup>S iota_constant)"
  unfolding singleton_standard_frame.is_unique_member_selector_def proof
    fix x
    assume "x \<in> elts (\<D>\<^sup>S i)"
    then have "x = 0"
      by simp
    moreover have "(\<^bold>\<lambda>z \<^bold>: \<D>\<^sup>S (i\<rightarrow>o)\<^bold>. 0) \<bullet> {0}\<^bsub>i\<^esub>\<^bsup>\<D>\<^sup>S\<^esup> = 0"
      using beta[OF singleton_standard_frame.one_element_function_is_domain_respecting]
      unfolding singleton_standard_domain_family.simps(3) by blast
    ultimately show "(\<J>\<^sup>S iota_constant) \<bullet> {x}\<^bsub>i\<^esub>\<^bsup>\<D>\<^sup>S\<^esup> = x"
      by fastforce
  qed
next
  show "\<forall>c \<alpha>. \<not> is_logical_constant (c, \<alpha>) \<longrightarrow> \<J>\<^sup>S (c, \<alpha>) \<in> elts (\<D>\<^sup>S \<alpha>)"
  proof (intro allI impI)
    fix c and \<alpha>
    assume "\<not> is_logical_constant (c, \<alpha>)"
    then have "\<J>\<^sup>S (c, \<alpha>) = (SOME z. z \<in> elts (\<D>\<^sup>S \<alpha>))"
      by auto
    moreover have "\<exists>z. z \<in> elts (\<D>\<^sup>S \<alpha>)"
      using eq0_iff and singleton_standard_frame.domain_nonemptiness by presburger
    then have "(SOME z. z \<in> elts (\<D>\<^sup>S \<alpha>)) \<in> elts (\<D>\<^sup>S \<alpha>)"
      using some_in_eq by auto
    ultimately show "\<J>\<^sup>S (c, \<alpha>) \<in> elts (\<D>\<^sup>S \<alpha>)"
      by auto
  qed
qed

fun singleton_standard_wff_denotation_function ("\<V>\<^sup>S") where
  "\<V>\<^sup>S \<phi> (x\<^bsub>\<alpha>\<^esub>) = \<phi> (x, \<alpha>)"
| "\<V>\<^sup>S \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = \<J>\<^sup>S (c, \<alpha>)"
| "\<V>\<^sup>S \<phi> (A \<sqdot> B) = (\<V>\<^sup>S \<phi> A) \<bullet> (\<V>\<^sup>S \<phi> B)"
| "\<V>\<^sup>S \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = (\<^bold>\<lambda>z \<^bold>: \<D>\<^sup>S \<alpha>\<^bold>. \<V>\<^sup>S (\<phi>((x, \<alpha>) := z)) A)"

lemma singleton_standard_wff_denotation_function_closure:
  assumes "frame.is_assignment \<D>\<^sup>S \<phi>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  shows "\<V>\<^sup>S \<phi> A \<in> elts (\<D>\<^sup>S \<alpha>)"
using assms(2,1) proof (induction A arbitrary: \<phi>)
  case (var_is_wff \<alpha> x)
  then show ?case
    by simp
next
  case (con_is_wff \<alpha> c)
  then show ?case
  proof (cases "(c, \<alpha>)" rule: constant_cases)
    case non_logical
    then show ?thesis
      using singleton_standard_premodel.non_logical_constant_denotation
      and singleton_standard_wff_denotation_function.simps(2) by presburger
  next
    case (Q_constant \<beta>)
    then have "\<V>\<^sup>S \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = q\<^bsub>\<beta>\<^esub>\<^bsup>\<D>\<^sup>S\<^esup>"
      by simp
    moreover have "q\<^bsub>\<beta>\<^esub>\<^bsup>\<D>\<^sup>S\<^esup> \<in> elts (\<D>\<^sup>S (\<beta>\<rightarrow>\<beta>\<rightarrow>o))"
      using singleton_standard_domain_family.simps(3)
      and singleton_standard_frame.identity_relation_is_domain_respecting by presburger
    ultimately show ?thesis
      using Q_constant by simp
  next
    case \<iota>_constant
    then have "\<V>\<^sup>S \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = (\<^bold>\<lambda>z \<^bold>: \<D>\<^sup>S (i\<rightarrow>o)\<^bold>. 0)"
      by simp
    moreover have "(\<^bold>\<lambda>z \<^bold>: \<D>\<^sup>S (i\<rightarrow>o)\<^bold>. 0) \<in> elts (\<D>\<^sup>S ((i\<rightarrow>o)\<rightarrow>i))"
      by (simp add: VPi_I)
    ultimately show ?thesis
      using \<iota>_constant by simp
  qed
next
  case (app_is_wff \<alpha> \<beta> A B)
  have "\<V>\<^sup>S \<phi> (A \<sqdot> B) = (\<V>\<^sup>S \<phi> A) \<bullet> (\<V>\<^sup>S \<phi> B)"
    using singleton_standard_wff_denotation_function.simps(3) .
  moreover have "\<V>\<^sup>S \<phi> A \<in> elts (\<D>\<^sup>S (\<alpha>\<rightarrow>\<beta>))" and "\<V>\<^sup>S \<phi> B \<in> elts (\<D>\<^sup>S \<alpha>)"
    using app_is_wff.IH and app_is_wff.prems by simp_all
  ultimately show ?case
    by (simp only: singleton_standard_frame.app_is_domain_respecting)
next
  case (abs_is_wff \<beta> A \<alpha> x)
  have "\<V>\<^sup>S \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = (\<^bold>\<lambda>z \<^bold>: \<D>\<^sup>S \<alpha>\<^bold>. \<V>\<^sup>S (\<phi>((x, \<alpha>) := z)) A)"
    using singleton_standard_wff_denotation_function.simps(4) .
  moreover have "\<V>\<^sup>S (\<phi>((x, \<alpha>) := z)) A \<in> elts (\<D>\<^sup>S \<beta>)" if "z \<in> elts (\<D>\<^sup>S \<alpha>)" for z
    using that and abs_is_wff.IH and abs_is_wff.prems by simp
  ultimately show ?case
    by (simp add: VPi_I)
qed

interpretation singleton_standard_model: standard_model "\<D>\<^sup>S" "\<J>\<^sup>S" "\<V>\<^sup>S"
proof (unfold_locales)
  show "singleton_standard_premodel.is_wff_denotation_function \<V>\<^sup>S"
    by (simp add: singleton_standard_wff_denotation_function_closure)
next
  show "\<forall>\<alpha> \<beta>. \<D>\<^sup>S (\<alpha>\<rightarrow>\<beta>) = \<D>\<^sup>S \<alpha> \<longmapsto> \<D>\<^sup>S \<beta>"
    using singleton_standard_domain_family.simps(3) by (intro allI)
qed

proposition standard_model_existence:
  shows "\<exists>\<M>. is_standard_model \<M>"
  using singleton_standard_model.standard_model_axioms by auto

subsection \<open>Theorem 5403 (Consistency Theorem)\<close>

proposition model_existence_implies_set_consistency:
  assumes "is_hyps \<G>"
  and "\<exists>\<M>. is_general_model \<M> \<and> is_model_for \<M> \<G>"
  shows "\<not> is_inconsistent_set \<G>"
proof (rule ccontr)
  from assms(2) obtain \<D> and \<J> and \<V> and \<M>
    where "\<M> = (\<D>, \<J>, \<V>)" and "is_model_for \<M> \<G>" and "is_general_model \<M>" by fastforce
  assume "\<not> \<not> is_inconsistent_set \<G>"
  then have "\<G> \<turnstile> F\<^bsub>o\<^esub>"
    by simp
  with \<open>is_general_model \<M>\<close> have "\<M> \<Turnstile> F\<^bsub>o\<^esub>"
    using thm_5402(2)[OF assms(1) \<open>is_model_for \<M> \<G>\<close>] by simp
  then have "\<V> \<phi> F\<^bsub>o\<^esub> = \<^bold>T" if "\<phi> \<leadsto> \<D>" for \<phi>
    using that and \<open>\<M> = (\<D>, \<J>, \<V>)\<close> by force
  moreover have "\<V> \<phi> F\<^bsub>o\<^esub> = \<^bold>F" if "\<phi> \<leadsto> \<D>" for \<phi>
    using \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and \<open>is_general_model \<M>\<close> and that and general_model.prop_5401_d
    by simp
  ultimately have "\<nexists>\<phi>. \<phi> \<leadsto> \<D>"
    by (auto simp add: inj_eq)
  moreover have "\<exists>\<phi>. \<phi> \<leadsto> \<D>"
  proof -
    \<comment> \<open>
      Since by definition domains are not empty then, by using the Axiom of Choice, we can specify
      an assignment \<open>\<psi>\<close> that simply chooses some element in the respective domain for each variable.
      Nonetheless, as pointed out in Footnote 11, page 19 in @{cite "andrews:1965"}, it is not
      necessary to use the Axiom of Choice to show that assignments exist since some assignments
      can be described explicitly.
    \<close>
    let ?\<psi> = "\<lambda>v. case v of (_, \<alpha>) \<Rightarrow> SOME z. z \<in> elts (\<D> \<alpha>)"
    from \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and \<open>is_general_model \<M>\<close> have "\<forall>\<alpha>. elts (\<D> \<alpha>) \<noteq> {}"
      using frame.domain_nonemptiness and premodel_def and general_model.axioms(1) by auto
    with \<open>\<M> = (\<D>, \<J>, \<V>)\<close> and \<open>is_general_model \<M>\<close> have "?\<psi> \<leadsto> \<D>"
      using frame.is_assignment_def and premodel_def and general_model.axioms(1)
      by (metis (mono_tags) case_prod_conv some_in_eq)
    then show ?thesis
      by (intro exI)
  qed
  ultimately show False ..
qed

proposition \<Q>\<^sub>0_is_consistent:
  shows "\<not> \<Q>\<^sub>0_is_inconsistent"
proof -
  have "\<exists>\<M>. is_general_model \<M> \<and> is_model_for \<M> {}"
    using standard_model_existence and standard_model.axioms(1) by blast
  then show ?thesis
    using model_existence_implies_set_consistency by simp
qed

lemmas thm_5403 = \<Q>\<^sub>0_is_consistent model_existence_implies_set_consistency

proposition principle_of_explosion:
  assumes "is_hyps \<G>"
  shows "is_inconsistent_set \<G> \<longleftrightarrow> (\<forall>A \<in> (wffs\<^bsub>o\<^esub>). \<G> \<turnstile> A)"
proof
  assume "is_inconsistent_set \<G>"
  show "\<forall>A \<in> (wffs\<^bsub>o\<^esub>). \<G> \<turnstile> A"
  proof
    fix A
    assume "A \<in> wffs\<^bsub>o\<^esub>"
    from \<open>is_inconsistent_set \<G>\<close> have "\<G> \<turnstile> F\<^bsub>o\<^esub>"
      unfolding is_inconsistent_set_def .
    then have "\<G> \<turnstile> \<forall>\<xx>\<^bsub>o\<^esub>. \<xx>\<^bsub>o\<^esub>"
      unfolding false_is_forall .
    with \<open>A \<in> wffs\<^bsub>o\<^esub>\<close> have "\<G> \<turnstile> \<^bold>S {(\<xx>, o) \<Zinj> A} (\<xx>\<^bsub>o\<^esub>)"
      using "\<forall>I" by fastforce
    then show "\<G> \<turnstile> A"
      by simp
  qed
next
  assume "\<forall>A \<in> (wffs\<^bsub>o\<^esub>). \<G> \<turnstile> A"
  then have "\<G> \<turnstile> F\<^bsub>o\<^esub>"
    using false_wff by (elim bspec)
  then show "is_inconsistent_set \<G>"
    unfolding is_inconsistent_set_def .
qed

end
