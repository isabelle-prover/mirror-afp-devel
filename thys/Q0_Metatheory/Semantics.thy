section \<open>Semantics\<close>

theory Semantics
  imports
    "ZFC_in_HOL.ZFC_Typeclasses"
    Syntax
    Boolean_Algebra
begin

no_notation funcset (infixr "\<rightarrow>" 60)
notation funcset (infixr "\<Zpfun>" 60)

abbreviation vfuncset :: "V \<Rightarrow> V \<Rightarrow> V" (infixr "\<longmapsto>" 60) where
  "A \<longmapsto> B \<equiv> VPi A (\<lambda>_. B)"

notation app (infixl "\<bullet>" 300)

syntax
  "_vlambda" :: "pttrn \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V" ("(3\<^bold>\<lambda>_\<^bold>:_ \<^bold>./ _)" [0, 0, 3] 3)
translations
  "\<^bold>\<lambda>x \<^bold>: A\<^bold>. f" \<rightleftharpoons> "CONST VLambda A (\<lambda>x. f)"

lemma vlambda_extensionality:
  assumes "\<And>x. x \<in> elts A \<Longrightarrow> f x = g x"
  shows "(\<^bold>\<lambda>x \<^bold>: A\<^bold>. f x) = (\<^bold>\<lambda>x \<^bold>: A\<^bold>. g x)"
  unfolding VLambda_def using assms by auto

subsection \<open>Frames\<close>

locale frame =
  fixes \<D> :: "type \<Rightarrow> V"
  assumes truth_values_domain_def: "\<D> o = \<bool>"
  and function_domain_def: "\<forall>\<alpha> \<beta>. \<D> (\<alpha>\<rightarrow>\<beta>) \<le> \<D> \<alpha> \<longmapsto> \<D> \<beta>"
  and domain_nonemptiness: "\<forall>\<alpha>. \<D> \<alpha> \<noteq> 0"
begin

lemma function_domainD:
  assumes "f \<in> elts (\<D> (\<alpha>\<rightarrow>\<beta>))"
  shows "f \<in> elts (\<D> \<alpha> \<longmapsto> \<D> \<beta>)"
  using assms and function_domain_def by blast

lemma vlambda_from_function_domain:
  assumes "f \<in> elts (\<D> (\<alpha>\<rightarrow>\<beta>))"
  obtains b where "f = (\<^bold>\<lambda>x \<^bold>: \<D> \<alpha>\<^bold>. b x)" and "\<forall>x \<in> elts (\<D> \<alpha>). b x \<in> elts (\<D> \<beta>)"
  using function_domainD[OF assms] by (metis VPi_D eta)

lemma app_is_domain_respecting:
  assumes "f \<in> elts (\<D> (\<alpha>\<rightarrow>\<beta>))" and "x \<in> elts (\<D> \<alpha>)"
  shows "f \<bullet> x \<in> elts (\<D> \<beta>)"
  by (fact VPi_D[OF function_domainD[OF assms(1)] assms(2)])

text \<open>One-element function on @{term \<open>\<D> \<alpha>\<close>}:\<close>

definition one_element_function :: "V \<Rightarrow> type \<Rightarrow> V" ("{_}\<^bsub>_\<^esub>" [901, 0] 900) where
  [simp]: "{x}\<^bsub>\<alpha>\<^esub> = (\<^bold>\<lambda>y \<^bold>: \<D> \<alpha>\<^bold>. bool_to_V (y = x))"

lemma one_element_function_is_domain_respecting:
  shows "{x}\<^bsub>\<alpha>\<^esub> \<in> elts (\<D> \<alpha> \<longmapsto> \<D> o)"
  unfolding one_element_function_def and truth_values_domain_def by (intro VPi_I) (simp, metis)

lemma one_element_function_simps:
  shows "x \<in> elts (\<D> \<alpha>) \<Longrightarrow> {x}\<^bsub>\<alpha>\<^esub> \<bullet> x = \<^bold>T"
  and "\<lbrakk>{x, y} \<subseteq> elts (\<D> \<alpha>); y \<noteq> x\<rbrakk> \<Longrightarrow> {x}\<^bsub>\<alpha>\<^esub> \<bullet> y = \<^bold>F"
  by simp_all

lemma one_element_function_injectivity:
  assumes "{x, x'} \<subseteq> elts (\<D> i)" and "{x}\<^bsub>i\<^esub> = {x'}\<^bsub>i\<^esub>"
  shows "x = x'"
  using assms(1) and VLambda_eq_D2[OF assms(2)[unfolded one_element_function_def]]
  and injD[OF bool_to_V_injectivity] by blast

lemma one_element_function_uniqueness:
  assumes "x \<in> elts (\<D> i)"
  shows "(SOME x'. x' \<in> elts (\<D> i) \<and> {x}\<^bsub>i\<^esub> = {x'}\<^bsub>i\<^esub>) = x"
  by (auto simp add: assms one_element_function_injectivity)

text \<open>Identity relation on @{term \<open>\<D> \<alpha>\<close>}:\<close>

definition identity_relation :: "type \<Rightarrow> V" ("q\<^bsub>_\<^esub>" [0] 100) where
  [simp]: "q\<^bsub>\<alpha>\<^esub> = (\<^bold>\<lambda>x \<^bold>: \<D> \<alpha>\<^bold>. {x}\<^bsub>\<alpha>\<^esub>)"

lemma identity_relation_is_domain_respecting:
  shows "q\<^bsub>\<alpha>\<^esub> \<in> elts (\<D> \<alpha> \<longmapsto> \<D> \<alpha> \<longmapsto> \<D> o)"
  using VPi_I and one_element_function_is_domain_respecting by simp

lemma q_is_equality:
  assumes "{x, y} \<subseteq> elts (\<D> \<alpha>)"
  shows "(q\<^bsub>\<alpha>\<^esub>) \<bullet> x \<bullet> y = \<^bold>T \<longleftrightarrow> x = y"
  unfolding identity_relation_def
  using assms and injD[OF bool_to_V_injectivity] by fastforce

text \<open>Unique member selector:\<close>

definition is_unique_member_selector :: "V \<Rightarrow> bool" where
  [iff]: "is_unique_member_selector f \<longleftrightarrow> (\<forall>x \<in> elts (\<D> i). f \<bullet> {x}\<^bsub>i\<^esub> = x)"

text \<open>Assignment:\<close>

definition is_assignment :: "(var \<Rightarrow> V) \<Rightarrow> bool" where
  [iff]: "is_assignment \<phi> \<longleftrightarrow> (\<forall>x \<alpha>. \<phi> (x, \<alpha>) \<in> elts (\<D> \<alpha>))"

end

abbreviation one_element_function_in ("{_}\<^bsub>_\<^esub>\<^bsup>_\<^esup>" [901, 0, 0] 900) where
  "{x}\<^bsub>\<alpha>\<^esub>\<^bsup>\<D>\<^esup> \<equiv> frame.one_element_function \<D> x \<alpha>"

abbreviation identity_relation_in ("q\<^bsub>_\<^esub>\<^bsup>_\<^esup>" [0, 0] 100) where
  "q\<^bsub>\<alpha>\<^esub>\<^bsup>\<D>\<^esup> \<equiv> frame.identity_relation \<D> \<alpha>"

text \<open>
  \<open>\<psi>\<close> is a ``\<open>v\<close>-variant'' of \<open>\<phi>\<close> if \<open>\<psi>\<close> is an assignment that agrees with \<open>\<phi>\<close> except possibly on
  \<open>v\<close>:
\<close>

definition is_variant_of :: "(var \<Rightarrow> V) \<Rightarrow> var \<Rightarrow> (var \<Rightarrow> V) \<Rightarrow> bool" ("_ \<sim>\<^bsub>_\<^esub> _" [51, 0, 51] 50) where
  [iff]: "\<psi> \<sim>\<^bsub>v\<^esub> \<phi> \<longleftrightarrow> (\<forall>v'. v' \<noteq> v \<longrightarrow> \<psi> v' = \<phi> v')"

subsection \<open>Pre-models (interpretations)\<close>

text \<open>We use the term ``pre-model'' instead of ``interpretation'' since the latter is already a keyword:\<close>

locale premodel = frame +
  fixes \<J> :: "con \<Rightarrow> V"
  assumes Q_denotation: "\<forall>\<alpha>. \<J> (Q_constant_of_type \<alpha>) = q\<^bsub>\<alpha>\<^esub>"
  and \<iota>_denotation: "is_unique_member_selector (\<J> iota_constant)"
  and non_logical_constant_denotation: "\<forall>c \<alpha>. \<not> is_logical_constant (c, \<alpha>) \<longrightarrow> \<J> (c, \<alpha>) \<in> elts (\<D> \<alpha>)"
begin

text \<open>Wff denotation function:\<close>

definition is_wff_denotation_function :: "((var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> V) \<Rightarrow> bool" where
  [iff]: "is_wff_denotation_function \<V> \<longleftrightarrow>
    (
      \<forall>\<phi>. is_assignment \<phi> \<longrightarrow>
        (\<forall>A \<alpha>. A \<in> wffs\<^bsub>\<alpha>\<^esub> \<longrightarrow> \<V> \<phi> A \<in> elts (\<D> \<alpha>)) \<and> \<comment> \<open>closure condition, see note in page 186\<close>
        (\<forall>x \<alpha>. \<V> \<phi> (x\<^bsub>\<alpha>\<^esub>) = \<phi> (x, \<alpha>)) \<and>
        (\<forall>c \<alpha>. \<V> \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = \<J> (c, \<alpha>)) \<and>
        (\<forall>A B \<alpha> \<beta>. A \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub> \<and> B \<in> wffs\<^bsub>\<beta>\<^esub> \<longrightarrow> \<V> \<phi> (A \<sqdot> B) = (\<V> \<phi> A) \<bullet> (\<V> \<phi> B)) \<and>
        (\<forall>x B \<alpha> \<beta>. B \<in> wffs\<^bsub>\<beta>\<^esub> \<longrightarrow> \<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) = (\<^bold>\<lambda>z \<^bold>: \<D> \<alpha>\<^bold>. \<V> (\<phi>((x, \<alpha>) := z)) B))
    )"

lemma wff_denotation_function_is_domain_respecting:
  assumes "is_wff_denotation_function \<V>"
  and "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
  and "is_assignment \<phi>"
  shows "\<V> \<phi> A \<in> elts (\<D> \<alpha>)"
  using assms by force

lemma wff_var_denotation:
  assumes "is_wff_denotation_function \<V>"
  and "is_assignment \<phi>"
  shows "\<V> \<phi> (x\<^bsub>\<alpha>\<^esub>) = \<phi> (x, \<alpha>)"
  using assms by force

lemma wff_Q_denotation:
  assumes "is_wff_denotation_function \<V>"
  and "is_assignment \<phi>"
  shows "\<V> \<phi> (Q\<^bsub>\<alpha>\<^esub>) = q\<^bsub>\<alpha>\<^esub>"
  using assms and Q_denotation by force

lemma wff_iota_denotation:
  assumes "is_wff_denotation_function \<V>"
  and "is_assignment \<phi>"
  shows "is_unique_member_selector (\<V> \<phi> \<iota>)"
  using assms and \<iota>_denotation by fastforce

lemma wff_non_logical_constant_denotation:
  assumes "is_wff_denotation_function \<V>"
  and "is_assignment \<phi>"
  and "\<not> is_logical_constant (c, \<alpha>)"
  shows "\<V> \<phi> (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = \<J> (c, \<alpha>)"
  using assms by auto

lemma wff_app_denotation:
  assumes "is_wff_denotation_function \<V>"
  and "is_assignment \<phi>"
  and "A \<in> wffs\<^bsub>\<beta>\<rightarrow>\<alpha>\<^esub>"
  and "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  shows "\<V> \<phi> (A \<sqdot> B) = \<V> \<phi> A \<bullet> \<V> \<phi> B"
  using assms by blast

lemma wff_abs_denotation:
  assumes "is_wff_denotation_function \<V>"
  and "is_assignment \<phi>"
  and "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  shows "\<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) = (\<^bold>\<lambda>z \<^bold>: \<D> \<alpha>\<^bold>. \<V> (\<phi>((x, \<alpha>) := z)) B)"
  using assms unfolding is_wff_denotation_function_def by metis

lemma wff_denotation_function_is_uniquely_determined:
  assumes "is_wff_denotation_function \<V>"
  and "is_wff_denotation_function \<V>'"
  and "is_assignment \<phi>"
  and "A \<in> wffs"
  shows "\<V> \<phi> A = \<V>' \<phi> A"
proof -
  obtain \<alpha> where "A \<in> wffs\<^bsub>\<alpha>\<^esub>"
    using assms(4) by blast
  then show ?thesis
  using assms(3) proof (induction A arbitrary: \<phi>)
    case var_is_wff
    with assms(1,2) show ?case
      by auto
  next
    case con_is_wff
    with assms(1,2) show ?case
      by auto
  next
    case app_is_wff
    with assms(1,2) show ?case
      using wff_app_denotation by metis
  next
    case (abs_is_wff \<beta> A \<alpha> x)
    have "is_assignment (\<phi>((x, \<alpha>) := z))" if "z \<in> elts (\<D> \<alpha>)" for z
      using that and abs_is_wff.prems by simp
    then have *: "\<V> (\<phi>((x, \<alpha>) := z)) A = \<V>' (\<phi>((x, \<alpha>) := z)) A" if "z \<in> elts (\<D> \<alpha>)" for z
      using abs_is_wff.IH and that by blast
    have "\<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = (\<^bold>\<lambda>z \<^bold>: \<D> \<alpha>\<^bold>. \<V> (\<phi>((x, \<alpha>) := z)) A)"
      by (fact wff_abs_denotation[OF assms(1) abs_is_wff.prems abs_is_wff.hyps])
    also have "\<dots> = (\<^bold>\<lambda>z \<^bold>: \<D> \<alpha>\<^bold>. \<V>' (\<phi>((x, \<alpha>) := z)) A)"
      using * and vlambda_extensionality by fastforce
    also have "\<dots> = \<V>' \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. A)"
      by (fact wff_abs_denotation[OF assms(2) abs_is_wff.prems abs_is_wff.hyps, symmetric])
    finally show ?case .
  qed
qed

end

subsection \<open>General models\<close>

type_synonym model_structure = "(type \<Rightarrow> V) \<times> (con \<Rightarrow> V) \<times> ((var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> V)"

text \<open>
  The assumption in the following locale implies that there must exist a function that is a wff
  denotation function for the pre-model, which is a requirement in the definition of general model
  in @{cite "andrews:2002"}:
\<close>

locale general_model = premodel +
  fixes \<V> :: "(var \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> V"
  assumes \<V>_is_wff_denotation_function: "is_wff_denotation_function \<V>"
begin

lemma mixed_beta_conversion:
  assumes "is_assignment \<phi>"
  and "y \<in> elts (\<D> \<alpha>)"
  and "B \<in> wffs\<^bsub>\<beta>\<^esub>"
  shows "\<V> \<phi> (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<bullet> y = \<V> (\<phi>((x, \<alpha>) := y)) B"
  using wff_abs_denotation[OF \<V>_is_wff_denotation_function assms(1,3)] and beta[OF assms(2)] by simp

lemma conj_fun_is_domain_respecting:
  assumes "is_assignment \<phi>"
  shows "\<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o))"
  using assms and conj_fun_wff and \<V>_is_wff_denotation_function by auto

lemma fully_applied_conj_fun_is_domain_respecting:
  assumes "is_assignment \<phi>"
  and "{x, y} \<subseteq> elts (\<D> o)"
  shows "\<V> \<phi> (\<and>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y \<in> elts (\<D> o)"
  using assms and conj_fun_is_domain_respecting and app_is_domain_respecting by (meson insert_subset)

lemma imp_fun_denotation_is_domain_respecting:
  assumes "is_assignment \<phi>"
  shows "\<V> \<phi> (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<in> elts (\<D> (o\<rightarrow>o\<rightarrow>o))"
  using assms and imp_fun_wff and \<V>_is_wff_denotation_function by simp

lemma fully_applied_imp_fun_denotation_is_domain_respecting:
  assumes "is_assignment \<phi>"
  and "{x, y} \<subseteq> elts (\<D> o)"
  shows "\<V> \<phi> (\<supset>\<^bsub>o\<rightarrow>o\<rightarrow>o\<^esub>) \<bullet> x \<bullet> y \<in> elts (\<D> o)"
  using assms and imp_fun_denotation_is_domain_respecting and app_is_domain_respecting
  by (meson insert_subset)

end

abbreviation is_general_model :: "model_structure \<Rightarrow> bool" where
  "is_general_model \<M> \<equiv> case \<M> of (\<D>, \<J>, \<V>) \<Rightarrow> general_model \<D> \<J> \<V>"

subsection \<open>Standard models\<close>

locale standard_model = general_model +
  assumes full_function_domain_def: "\<forall>\<alpha> \<beta>. \<D> (\<alpha>\<rightarrow>\<beta>) = \<D> \<alpha> \<longmapsto> \<D> \<beta>"

abbreviation is_standard_model :: "model_structure \<Rightarrow> bool" where
  "is_standard_model \<M> \<equiv> case \<M> of (\<D>, \<J>, \<V>) \<Rightarrow> standard_model \<D> \<J> \<V>"

lemma standard_model_is_general_model:
  assumes "is_standard_model \<M>"
  shows "is_general_model \<M>"
  using assms and standard_model.axioms(1) by force

subsection \<open>Validity\<close>

abbreviation is_assignment_into_frame ("_ \<leadsto> _" [51, 51] 50) where
  "\<phi> \<leadsto> \<D> \<equiv> frame.is_assignment \<D> \<phi>"

abbreviation is_assignment_into_model ("_ \<leadsto>\<^sub>M _" [51, 51] 50) where
  "\<phi> \<leadsto>\<^sub>M \<M> \<equiv> (case \<M> of (\<D>, \<J>, \<V>) \<Rightarrow> \<phi> \<leadsto> \<D>)"

abbreviation satisfies ("_ \<Turnstile>\<^bsub>_\<^esub> _" [50, 50, 50] 50) where
  "\<M> \<Turnstile>\<^bsub>\<phi>\<^esub> A \<equiv> case \<M> of (\<D>, \<J>, \<V>) \<Rightarrow> \<V> \<phi> A = \<^bold>T"

abbreviation is_satisfiable_in where
  "is_satisfiable_in A \<M> \<equiv> \<exists>\<phi>. \<phi> \<leadsto>\<^sub>M \<M> \<and> \<M> \<Turnstile>\<^bsub>\<phi>\<^esub> A"

abbreviation is_valid_in ("_ \<Turnstile> _" [50, 50] 50) where
  "\<M> \<Turnstile> A \<equiv> \<forall>\<phi>. \<phi> \<leadsto>\<^sub>M \<M> \<longrightarrow> \<M> \<Turnstile>\<^bsub>\<phi>\<^esub> A"

abbreviation is_valid_in_the_general_sense ("\<Turnstile> _" [50] 50) where
  "\<Turnstile> A \<equiv> \<forall>\<M>. is_general_model \<M> \<longrightarrow> \<M> \<Turnstile> A"

abbreviation is_valid_in_the_standard_sense ("\<Turnstile>\<^sub>S _" [50] 50) where
  "\<Turnstile>\<^sub>S A \<equiv> \<forall>\<M>. is_standard_model \<M> \<longrightarrow> \<M> \<Turnstile> A"

abbreviation is_true_sentence_in where
  "is_true_sentence_in A \<M> \<equiv> is_sentence A \<and> \<M> \<Turnstile>\<^bsub>undefined\<^esub> A" \<comment> \<open>assignments are not meaningful\<close>

abbreviation is_false_sentence_in where
  "is_false_sentence_in A \<M> \<equiv> is_sentence A \<and> \<not> \<M> \<Turnstile>\<^bsub>undefined\<^esub> A" \<comment> \<open>assignments are not meaningful\<close>

abbreviation is_model_for where
  "is_model_for \<M> \<G> \<equiv> \<forall>A \<in> \<G>. \<M> \<Turnstile> A"

lemma general_validity_in_standard_validity:
  assumes "\<Turnstile> A"
  shows "\<Turnstile>\<^sub>S A"
  using assms and standard_model_is_general_model by blast

end
