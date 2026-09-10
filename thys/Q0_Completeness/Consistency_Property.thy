theory Consistency_Property imports
  "Abstract_Consistency_Property.Abstract_Consistency_Property"
  "Q0_Metatheory.Syntax"
begin

section \<open>Consistency Property\<close>

inductive confl_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<crossmark>\<close> 50) where
  CFalse: \<open>[] \<leadsto>\<^sub>\<crossmark> [ F\<^bsub>o\<^esub> ]\<close>
| CNot: \<open>[ \<sim>\<^sup>\<Q> A ] \<leadsto>\<^sub>\<crossmark> [ A ]\<close> if \<open>A \<in> wffs\<^bsub>o\<^esub>\<close>

inductive alpha_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<alpha>\<close> 50) where
  CBool: \<open>[ A ] \<leadsto>\<^sub>\<alpha> [ A =\<^bsub>o\<^esub> T\<^bsub>o\<^esub> ]\<close> if \<open>A \<in> wffs\<^bsub>o\<^esub>\<close>
| CIota: \<open>[] \<leadsto>\<^sub>\<alpha> [ \<iota> \<sqdot> (Q\<^bsub>i\<^esub> \<sqdot> A) =\<^bsub>i\<^esub> A ]\<close> if \<open>A \<in> wffs\<^bsub>i\<^esub>\<close>
| CRefl: \<open>[] \<leadsto>\<^sub>\<alpha> [ A =\<^bsub>\<alpha>\<^esub> A ]\<close> if \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close>
| CTrans: \<open>[ A =\<^bsub>\<alpha>\<^esub> B, B =\<^bsub>\<alpha>\<^esub> C ] \<leadsto>\<^sub>\<alpha> [ A =\<^bsub>\<alpha>\<^esub> C ]\<close> if \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>C \<in> wffs\<^bsub>\<alpha>\<^esub>\<close>
| CCong: \<open>[ A =\<^bsub>\<alpha>\<^esub> B ] \<leadsto>\<^sub>\<alpha> [ C \<sqdot> A =\<^bsub>\<beta>\<^esub> C \<sqdot> B ]\<close> if \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>C \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub>\<close>
| CSubst: \<open>[] \<leadsto>\<^sub>\<alpha> [ (\<lambda>x\<^bsub>\<alpha>\<^esub>. B) \<sqdot> A =\<^bsub>\<beta>\<^esub> \<^bold>S {(x, \<alpha>) \<Zinj> A} B ]\<close> if
  \<open>A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>\<beta>\<^esub>\<close> and \<open>free_vars A = {}\<close>

inductive beta_class :: \<open>form list \<Rightarrow> form list \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<beta>\<close> 50) where
  CLEM: \<open>[] \<leadsto>\<^sub>\<beta> [ A, \<sim>\<^sup>\<Q> A ]\<close> if \<open>A \<in> wffs\<^bsub>o\<^esub>\<close>

inductive gamma_class :: \<open>form list \<Rightarrow> (form set \<Rightarrow> _) \<times> (form \<Rightarrow> _) \<Rightarrow> bool\<close> (infix \<open>\<leadsto>\<^sub>\<gamma>\<close> 50) where
  CExt: \<open>[ A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B ] \<leadsto>\<^sub>\<gamma> (\<lambda>_. wffs\<^bsub>\<alpha>\<^esub>, \<lambda>C. [ A \<sqdot> C =\<^bsub>\<beta>\<^esub> B \<sqdot> C ])\<close> if
  \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub>\<close> and \<open>B \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub>\<close>

subsection \<open>Negated Equality\<close>

inductive ineq_match :: \<open>form \<Rightarrow> type \<times> type \<times> form \<times> form \<Rightarrow> bool\<close> where
  \<open>ineq_match (\<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)) (\<alpha>, \<beta>, A, B)\<close>

inductive_cases ineq_matchE [elim]: \<open>ineq_match (\<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)) (\<alpha>', \<beta>', A', B')\<close>

lemma ineq_match_uniq [dest]:
  assumes \<open>ineq_match C (\<alpha>, \<beta>, A, B)\<close>
    and \<open>ineq_match C (\<alpha>', \<beta>', A', B')\<close>
  shows \<open>\<alpha> = \<alpha>' \<and> \<beta> = \<beta>' \<and> A = A' \<and> B = B'\<close>
  using assms by (auto elim: ineq_match.cases)

lemma THE_ineq_match:
  assumes \<open>ineq_match C (\<alpha>, \<beta>, A, B)\<close>
  shows \<open>(THE (\<alpha>, \<beta>, A, B). ineq_match C (\<alpha>, \<beta>, A, B)) = (\<alpha>, \<beta>, A, B)\<close>
  using assms by blast

lemma ineq_matchD [dest]:
  assumes \<open>ineq_match C (\<alpha>, \<beta>, A, B)\<close>
  shows \<open>C = \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)\<close>
  using assms by (auto elim!: ineq_match.cases)

lemma ineq_matchI [intro]:
  assumes \<open>C = \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)\<close>
  shows \<open>ineq_match C (\<alpha>, \<beta>, A, B)\<close>
  using assms ineq_match.intros by blast

subsection \<open>Delta\<close>

fun delta :: \<open>form \<Rightarrow> nat \<Rightarrow> form list\<close> where
  CDelta: \<open>delta C c =
    (if C \<in> wffs\<^bsub>o\<^esub> \<and> (\<exists>\<alpha> \<beta> A B. ineq_match C (\<alpha>, \<beta>, A, B)) then
       case THE (\<alpha>, \<beta>, A, B). ineq_match C (\<alpha>, \<beta>, A, B) of
         (\<alpha>, \<beta>, A, B) \<Rightarrow> [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]
     else [])\<close>

lemma ineq_match_delta [simp]:
  assumes \<open>C \<in> wffs\<^bsub>o\<^esub>\<close> \<open>ineq_match C (\<alpha>, \<beta>, A, B)\<close>
  shows \<open>delta C c = [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
  unfolding CDelta using assms THE_ineq_match by auto

lemma delta:
  assumes \<open>A \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub>\<close> \<open>B \<in> wffs\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub>\<close>
  shows \<open>delta (\<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)) c = [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
  using assms equality_wff ineq_matchI ineq_match_delta neg_wff by metis

subsection \<open>Operations\<close>

definition \<open>logical_names \<equiv> {\<cc>\<^sub>Q, \<cc>\<^sub>\<iota>}\<close>
abbreviation \<open>is_logical_name c \<equiv> c \<in> logical_names\<close>

lemma logical_name_simps[simp]:
  shows \<open>is_logical_name \<cc>\<^sub>Q\<close>
    and \<open>is_logical_name \<cc>\<^sub>\<iota>\<close>
  by (simp_all add: logical_names_def)

definition \<open>is_param c \<equiv> \<not> is_logical_name c\<close>

fun map_con :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> form \<Rightarrow> form\<close> where
  \<open>map_con _ (x\<^bsub>\<alpha>\<^esub>) = (x\<^bsub>\<alpha>\<^esub>)\<close>
| \<open>map_con f (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = (if is_logical_name c \<or> is_logical_name (f c) then \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> else \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>)\<close>
| \<open>map_con f (A \<sqdot> B) = map_con f A \<sqdot> map_con f B\<close>
| \<open>map_con f (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = \<lambda>x\<^bsub>\<alpha>\<^esub>. map_con f A\<close>

fun cons_form :: \<open>form \<Rightarrow> nat set\<close> where
  \<open>cons_form (x\<^bsub>\<alpha>\<^esub>) = {}\<close>
| \<open>cons_form (\<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) = (if is_logical_name c then {} else {c})\<close>
| \<open>cons_form (A \<sqdot> B) = cons_form A \<union> cons_form B\<close>
| \<open>cons_form (\<lambda>x\<^bsub>\<alpha>\<^esub>. A) = cons_form A\<close>

subsection \<open>Lemmas\<close>

text \<open>This property is really what dodging the logical constants is all about.\<close>
proposition \<open>map_con f (\<sim>\<^sup>\<Q> A) = \<sim>\<^sup>\<Q> (map_con f A)\<close>
  by simp

lemma map_con_id [simp]: \<open>map_con id = id\<close>
proof
  fix A
  show \<open>map_con id A = id A\<close>
    by (induct A) auto
qed

lemma map_con_cong [simp]:
  assumes \<open>\<forall>x \<in> cons_form A. f x = g x\<close>
  shows \<open>map_con f A = map_con g A\<close>
  using assms by (induct A) auto

lemma wff_map_con [iff]: \<open>map_con f A \<in> wffs\<^bsub>\<alpha>\<^esub> \<longleftrightarrow> A \<in> wffs\<^bsub>\<alpha>\<^esub>\<close>
proof (induct A arbitrary: \<alpha>)
  case (FVar x)
  then show ?case
    by (metis map_con.simps(1) surj_pair)
next
  case (FCon x)
  then show ?case
    by (induct x) (auto dest: wff_has_unique_type)
next
  case (FApp A B)
  then show ?case
    by (metis map_con.simps(3) wffs_from_app wffs_of_type_intros(3))
next
  case (FAbs x1a A)
  then show ?case
    by (metis map_con.simps(4) surj_pair wffs_from_abs wffs_of_type_intros(4))
qed

lemma finite_cons_form [simp]: \<open>finite (cons_form A)\<close>
  by (induct A) auto

lemma map_con_ineq_match [intro]: 
  assumes \<open>ineq_match C (\<alpha>, \<beta>, A, B)\<close>
  shows \<open>ineq_match (map_con f C) (\<alpha>, \<beta>, map_con f A, map_con f B)\<close>
  using assms
  by (auto elim: ineq_match.cases simp: ineq_match.simps)

lemma free_vars_map_con [simp]: \<open>free_vars (map_con f A) = free_vars A\<close>
  by (induct A) (auto split: if_splits)

lemma map_con_substitute [simp]: \<open>map_con f (substitute {(x, \<alpha>) \<Zinj> A} B) 
  = substitute {(x, \<alpha>) \<Zinj> map_con f A} (map_con f B)\<close>
  using singleton_substitution_simps by (induct B) auto

subsection \<open>Parameter Substitution Inversion\<close>

lemma map_con_FVar [dest]: \<open>map_con f A = x\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A = x\<^bsub>\<alpha>\<^esub>\<close>
  by (induct A) (auto split: if_splits)

lemma map_con_FCon_not_param [dest]: \<open>map_con f A = \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> \<Longrightarrow> \<not> is_param c \<Longrightarrow> A = \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>\<close>
  unfolding is_param_def by (induct A) (auto split: if_splits)

lemma map_con_FApp [dest!]: 
  assumes \<open>map_con f A = B \<sqdot> C\<close>
  shows \<open>\<exists>B' C'. map_con f B' = B \<and> map_con f C' = C \<and> A = B' \<sqdot> C'\<close>
  using assms
  by (induct A) (auto split: if_splits)

lemma map_con_FAbs [dest!]: 
  assumes \<open>map_con f A = \<lambda>x\<^bsub>\<alpha>\<^esub>. B\<close>
  shows \<open>\<exists>B'. map_con f B' = B \<and> A = \<lambda>x\<^bsub>\<alpha>\<^esub>. B'\<close>
  using assms
  by (induct A) (auto split: if_splits)

lemma map_con_cQ [dest]: \<open>map_con f A = \<lbrace>\<cc>\<^sub>Q\<rbrace>\<^bsub>\<alpha>\<^esub> \<Longrightarrow> A = \<lbrace>\<cc>\<^sub>Q\<rbrace>\<^bsub>\<alpha>\<^esub>\<close>
  by (auto simp: is_param_def)

lemma map_con_equality_of_type [dest]: 
  assumes \<open>map_con f A = B =\<^bsub>\<alpha>\<^esub> C\<close>
  shows \<open>\<exists>B' C'. map_con f B' = B \<and> map_con f C' = C \<and> A = B' =\<^bsub>\<alpha>\<^esub> C'\<close>
  using assms
  by fastforce

lemma map_con_neg [dest]: \<open>map_con f A = \<sim>\<^sup>\<Q> B \<Longrightarrow> \<exists>B'. map_con f B' = B \<and> A = \<sim>\<^sup>\<Q> B'\<close>
  by (induct A) auto

lemma ineq_match_map_con [dest]:
  assumes \<open>ineq_match (map_con f C) (\<alpha>, \<beta>, A, B)\<close>
  shows \<open>\<exists>A' B'. map_con f A' = A \<and> map_con f B' = B \<and> ineq_match C (\<alpha>, \<beta>, A', B')\<close>
  using assms
  by fast

subsection \<open>Interpretations\<close>

interpretation P: Params map_con cons_form is_param
  by unfold_locales simp_all

interpretation C: Confl map_con cons_form is_param confl_class
  by unfold_locales (fastforce elim!: confl_class.cases simp: confl_class.simps)

interpretation A: Alpha map_con cons_form is_param alpha_class
proof (unfold_locales, safe?)
  fix ps qs f
  assume \<open>ps \<leadsto>\<^sub>\<alpha> qs\<close>
  then show \<open>map (map_con f) ps \<leadsto>\<^sub>\<alpha> map (map_con f) qs\<close>
    by (elim alpha_class.cases) (auto simp: alpha_class.simps)
qed

interpretation B: Beta map_con cons_form is_param beta_class
  by unfold_locales (auto elim!: beta_class.cases simp: beta_class.simps)

interpretation G: Gamma map_con map_con cons_form is_param gamma_class
  by unfold_locales (elim gamma_class.cases, auto simp: gamma_class.simps)

interpretation D: Delta map_con cons_form is_param delta
proof
  fix p x f
  assume \<open>is_param x\<close> \<open>P.is_subst f\<close>
  then show \<open>delta (map_con f p) (f x) = map (map_con f) (delta p x)\<close>
  proof (induct p x rule: delta.induct)
    case (1 C c)
    then have c: \<open>\<not> is_logical_name (f c)\<close>
      unfolding P.is_subst_def by (auto simp: is_param_def)

    from 1 show ?case
    proof (cases \<open>C \<in> wffs\<^bsub>o\<^esub> \<and> (\<exists>\<alpha> \<beta> A B. ineq_match C (\<alpha>, \<beta>, A, B))\<close>)
      case True
      then obtain \<alpha> \<beta> A B where C: \<open>C = \<sim>\<^sup>\<Q> (A =\<^bsub>\<alpha> \<rightarrow> \<beta>\<^esub> B)\<close>
        by fast
      then have *: \<open>delta C c = [ \<sim>\<^sup>\<Q> (A \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> B \<sqdot> \<lbrace>c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        using True CDelta ineq_match_delta by blast
      then have *: \<open>map (map_con f) (delta C c) = [ \<sim>\<^sup>\<Q> (map_con f A \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> map_con f B \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        using 1 c by (auto simp: is_param_def)
      have \<open>ineq_match (map_con f C) (\<alpha>, \<beta>, map_con f A, map_con f B)\<close>
        using C map_con_ineq_match by blast
      moreover have \<open>map_con f C \<in> wffs\<^bsub>o\<^esub>\<close>
        using True wff_map_con by blast
      ultimately have \<open>delta (map_con f C) (f c) = [ \<sim>\<^sup>\<Q> (map_con f A \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub> =\<^bsub>\<beta>\<^esub> map_con f B \<sqdot> \<lbrace>f c\<rbrace>\<^bsub>\<alpha>\<^esub>) ]\<close>
        unfolding CDelta using ineq_match_delta by auto
      then show ?thesis
        using * by simp
    next
      case False
      then show ?thesis
        by auto
    qed
  qed
qed

abbreviation Kinds :: \<open>(nat, form) kind list\<close> where
  \<open>Kinds \<equiv> [C.kind, A.kind, B.kind, G.kind, D.kind]\<close>

lemma prop\<^sub>E_Kinds:
  assumes \<open>P.sat\<^sub>E C.kind C\<close> \<open>P.sat\<^sub>E A.kind C\<close>  \<open>P.sat\<^sub>E B.kind C\<close> \<open>P.sat\<^sub>E G.kind C\<close> \<open>P.sat\<^sub>E D.kind C\<close>
  shows \<open>P.prop\<^sub>E Kinds C\<close>
  unfolding P.prop\<^sub>E_def using assms by simp

interpretation Consistency_Kinds map_con cons_form is_param Kinds
  using P.Params_axioms C.Consistency_Kind_axioms A.Consistency_Kind_axioms B.Consistency_Kind_axioms
    G.Consistency_Kind_axioms D.Consistency_Kind_axioms
  by (auto intro: Consistency_Kinds.intro simp: Consistency_Kinds_axioms_def)

interpretation Maximal_Consistency map_con cons_form is_param Kinds
proof
  have \<open>infinite (UNIV :: form set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>A. A \<sqdot> A\<close>] by simp
  then show \<open>infinite (UNIV :: form set)\<close>
    using finite_prod by blast
qed simp

end
