section \<open>Propositional Well-Formed Formulas\<close>

theory Propositional_Wff
  imports
    Syntax
    Boolean_Algebra
begin

subsection \<open>Syntax\<close>

inductive_set pwffs :: "form set" where
  T_pwff: "T\<^bsub>o\<^esub> \<in> pwffs"
| F_pwff: "F\<^bsub>o\<^esub> \<in> pwffs"
| var_pwff: "p\<^bsub>o\<^esub> \<in> pwffs"
| neg_pwff: "\<sim>\<^sup>\<Q> A \<in> pwffs" if "A \<in> pwffs"
| conj_pwff: "A \<and>\<^sup>\<Q> B \<in> pwffs" if "A \<in> pwffs" and "B \<in> pwffs"
| disj_pwff: "A \<or>\<^sup>\<Q> B \<in> pwffs" if "A \<in> pwffs" and "B \<in> pwffs"
| imp_pwff: "A \<supset>\<^sup>\<Q> B \<in> pwffs" if "A \<in> pwffs" and "B \<in> pwffs"
| eqv_pwff: "A \<equiv>\<^sup>\<Q> B \<in> pwffs" if "A \<in> pwffs" and "B \<in> pwffs"

lemmas [intro!] = pwffs.intros

lemma pwffs_distinctnesses [induct_simp]:
  shows "T\<^bsub>o\<^esub> \<noteq> F\<^bsub>o\<^esub>"
  and "T\<^bsub>o\<^esub> \<noteq> p\<^bsub>o\<^esub>"
  and "T\<^bsub>o\<^esub> \<noteq> \<sim>\<^sup>\<Q> A"
  and "T\<^bsub>o\<^esub> \<noteq> A \<and>\<^sup>\<Q> B"
  and "T\<^bsub>o\<^esub> \<noteq> A \<or>\<^sup>\<Q> B"
  and "T\<^bsub>o\<^esub> \<noteq> A \<supset>\<^sup>\<Q> B"
  and "T\<^bsub>o\<^esub> \<noteq> A \<equiv>\<^sup>\<Q> B"
  and "F\<^bsub>o\<^esub> \<noteq> p\<^bsub>o\<^esub>"
  and "F\<^bsub>o\<^esub> \<noteq> \<sim>\<^sup>\<Q> A"
  and "F\<^bsub>o\<^esub> \<noteq> A \<and>\<^sup>\<Q> B"
  and "F\<^bsub>o\<^esub> \<noteq> A \<or>\<^sup>\<Q> B"
  and "F\<^bsub>o\<^esub> \<noteq> A \<supset>\<^sup>\<Q> B"
  and "F\<^bsub>o\<^esub> \<noteq> A \<equiv>\<^sup>\<Q> B"
  and "p\<^bsub>o\<^esub> \<noteq> \<sim>\<^sup>\<Q> A"
  and "p\<^bsub>o\<^esub> \<noteq> A \<and>\<^sup>\<Q> B"
  and "p\<^bsub>o\<^esub> \<noteq> A \<or>\<^sup>\<Q> B"
  and "p\<^bsub>o\<^esub> \<noteq> A \<supset>\<^sup>\<Q> B"
  and "p\<^bsub>o\<^esub> \<noteq> A \<equiv>\<^sup>\<Q> B"
  and "\<sim>\<^sup>\<Q> A \<noteq> B \<and>\<^sup>\<Q> C"
  and "\<sim>\<^sup>\<Q> A \<noteq> B \<or>\<^sup>\<Q> C"
  and "\<sim>\<^sup>\<Q> A \<noteq> B \<supset>\<^sup>\<Q> C"
  and "\<not> (B = F\<^bsub>o\<^esub> \<and> A = C) \<Longrightarrow> \<sim>\<^sup>\<Q> A \<noteq> B \<equiv>\<^sup>\<Q> C" \<comment> \<open>\<^term>\<open>\<sim>\<^sup>\<Q> A\<close> is the same as \<^term>\<open>F\<^bsub>o\<^esub> \<equiv>\<^sup>\<Q> A\<close>\<close>
  and "A \<and>\<^sup>\<Q> B \<noteq> C \<or>\<^sup>\<Q> D"
  and "A \<and>\<^sup>\<Q> B \<noteq> C \<supset>\<^sup>\<Q> D"
  and "A \<and>\<^sup>\<Q> B \<noteq> C \<equiv>\<^sup>\<Q> D"
  and "A \<or>\<^sup>\<Q> B \<noteq> C \<supset>\<^sup>\<Q> D"
  and "A \<or>\<^sup>\<Q> B \<noteq> C \<equiv>\<^sup>\<Q> D"
  and "A \<supset>\<^sup>\<Q> B \<noteq> C \<equiv>\<^sup>\<Q> D"
  by simp_all

lemma pwffs_injectivities [induct_simp]:
  shows "\<sim>\<^sup>\<Q> A = \<sim>\<^sup>\<Q> A' \<Longrightarrow> A = A'"
  and "A \<and>\<^sup>\<Q> B = A' \<and>\<^sup>\<Q> B' \<Longrightarrow> A = A' \<and> B = B'"
  and "A \<or>\<^sup>\<Q> B = A' \<or>\<^sup>\<Q> B' \<Longrightarrow> A = A' \<and> B = B'"
  and "A \<supset>\<^sup>\<Q> B = A' \<supset>\<^sup>\<Q> B' \<Longrightarrow> A = A' \<and> B = B'"
  and "A \<equiv>\<^sup>\<Q> B = A' \<equiv>\<^sup>\<Q> B' \<Longrightarrow> A = A' \<and> B = B'"
  by simp_all

lemma pwff_from_neg_pwff [elim!]:
  assumes "\<sim>\<^sup>\<Q> A \<in> pwffs"
  shows "A \<in> pwffs"
  using assms by cases simp_all

lemma pwffs_from_conj_pwff [elim!]:
  assumes "A \<and>\<^sup>\<Q> B \<in> pwffs"
  shows "{A, B} \<subseteq> pwffs"
  using assms by cases simp_all

lemma pwffs_from_disj_pwff [elim!]:
  assumes "A \<or>\<^sup>\<Q> B \<in> pwffs"
  shows "{A, B} \<subseteq> pwffs"
  using assms by cases simp_all

lemma pwffs_from_imp_pwff [elim!]:
  assumes "A \<supset>\<^sup>\<Q> B \<in> pwffs"
  shows "{A, B} \<subseteq> pwffs"
  using assms by cases simp_all

lemma pwffs_from_eqv_pwff [elim!]:
  assumes "A \<equiv>\<^sup>\<Q> B \<in> pwffs"
  shows "{A, B} \<subseteq> pwffs"
  using assms by cases (simp_all, use F_pwff in fastforce)

lemma pwffs_subset_of_wffso:
  shows "pwffs \<subseteq> wffs\<^bsub>o\<^esub>"
proof
  fix A
  assume "A \<in> pwffs"
  then show "A \<in> wffs\<^bsub>o\<^esub>"
    by induction auto
qed

lemma pwff_free_vars_simps [simp]:
  shows T_fv: "free_vars T\<^bsub>o\<^esub> = {}"
  and F_fv: "free_vars F\<^bsub>o\<^esub> = {}"
  and var_fv: "free_vars (p\<^bsub>o\<^esub>) = {(p, o)}"
  and neg_fv: "free_vars (\<sim>\<^sup>\<Q> A) = free_vars A"
  and conj_fv: "free_vars (A \<and>\<^sup>\<Q> B) = free_vars A \<union> free_vars B"
  and disj_fv: "free_vars (A \<or>\<^sup>\<Q> B) = free_vars A \<union> free_vars B"
  and imp_fv: "free_vars (A \<supset>\<^sup>\<Q> B) = free_vars A \<union> free_vars B"
  and eqv_fv: "free_vars (A \<equiv>\<^sup>\<Q> B) = free_vars A \<union> free_vars B"
  by force+

lemma pwffs_free_vars_are_propositional:
  assumes "A \<in> pwffs"
  and "v \<in> free_vars A"
  obtains p where "v = (p, o)"
using assms by (induction A arbitrary: thesis) auto

lemma is_free_for_in_pwff [intro]:
  assumes "A \<in> pwffs"
  and "v \<in> free_vars A"
  shows "is_free_for B v A"
using assms proof (induction A)
  case (neg_pwff C)
  then show ?case
    using is_free_for_in_neg by simp
next
  case (conj_pwff C D)
  from conj_pwff.prems consider
    (a) "v \<in> free_vars C" and "v \<in> free_vars D"
  | (b) "v \<in> free_vars C" and "v \<notin> free_vars D"
  | (c) "v \<notin> free_vars C" and "v \<in> free_vars D"
    by auto
  then show ?case
  proof cases
    case a
    then show ?thesis
      using conj_pwff.IH by (intro is_free_for_in_conj)
  next
    case b
    have "is_free_for B v C"
      by (fact conj_pwff.IH(1)[OF b(1)])
    moreover from b(2) have "is_free_for B v D"
      using is_free_at_in_free_vars by blast
    ultimately show ?thesis
      by (rule is_free_for_in_conj)
  next
    case c
    from c(1) have "is_free_for B v C"
      using is_free_at_in_free_vars by blast
    moreover have "is_free_for B v D"
      by (fact conj_pwff.IH(2)[OF c(2)])
    ultimately show ?thesis
      by (rule is_free_for_in_conj)
  qed
next
  case (disj_pwff C D)
  from disj_pwff.prems consider
    (a) "v \<in> free_vars C" and "v \<in> free_vars D"
  | (b) "v \<in> free_vars C" and "v \<notin> free_vars D"
  | (c) "v \<notin> free_vars C" and "v \<in> free_vars D"
    by auto
  then show ?case
  proof cases
    case a
    then show ?thesis
      using disj_pwff.IH by (intro is_free_for_in_disj)
  next
    case b
    have "is_free_for B v C"
      by (fact disj_pwff.IH(1)[OF b(1)])
    moreover from b(2) have "is_free_for B v D"
      using is_free_at_in_free_vars by blast
    ultimately show ?thesis
      by (rule is_free_for_in_disj)
  next
    case c
    from c(1) have "is_free_for B v C"
      using is_free_at_in_free_vars by blast
    moreover have "is_free_for B v D"
      by (fact disj_pwff.IH(2)[OF c(2)])
    ultimately show ?thesis
      by (rule is_free_for_in_disj)
  qed
next
  case (imp_pwff C D)
  from imp_pwff.prems consider
    (a) "v \<in> free_vars C" and "v \<in> free_vars D"
  | (b) "v \<in> free_vars C" and "v \<notin> free_vars D"
  | (c) "v \<notin> free_vars C" and "v \<in> free_vars D"
    by auto
  then show ?case
  proof cases
    case a
    then show ?thesis
      using imp_pwff.IH by (intro is_free_for_in_imp)
  next
    case b
    have "is_free_for B v C"
      by (fact imp_pwff.IH(1)[OF b(1)])
    moreover from b(2) have "is_free_for B v D"
      using is_free_at_in_free_vars by blast
    ultimately show ?thesis
      by (rule is_free_for_in_imp)
  next
    case c
    from c(1) have "is_free_for B v C"
      using is_free_at_in_free_vars by blast
    moreover have "is_free_for B v D"
      by (fact imp_pwff.IH(2)[OF c(2)])
    ultimately show ?thesis
      by (rule is_free_for_in_imp)
  qed
next
  case (eqv_pwff C D)
  from eqv_pwff.prems consider
    (a) "v \<in> free_vars C" and "v \<in> free_vars D"
  | (b) "v \<in> free_vars C" and "v \<notin> free_vars D"
  | (c) "v \<notin> free_vars C" and "v \<in> free_vars D"
    by auto
  then show ?case
  proof cases
    case a
    then show ?thesis
      using eqv_pwff.IH by (intro is_free_for_in_equivalence)
  next
    case b
    have "is_free_for B v C"
      by (fact eqv_pwff.IH(1)[OF b(1)])
    moreover from b(2) have "is_free_for B v D"
      using is_free_at_in_free_vars by blast
    ultimately show ?thesis
      by (rule is_free_for_in_equivalence)
  next
    case c
    from c(1) have "is_free_for B v C"
      using is_free_at_in_free_vars by blast
    moreover have "is_free_for B v D"
      by (fact eqv_pwff.IH(2)[OF c(2)])
    ultimately show ?thesis
      by (rule is_free_for_in_equivalence)
  qed
qed auto

subsection \<open>Semantics\<close>

text \<open>Assignment of truth values to propositional variables:\<close>

definition is_tv_assignment :: "(nat \<Rightarrow> V) \<Rightarrow> bool" where
  [iff]: "is_tv_assignment \<phi> \<longleftrightarrow> (\<forall>p. \<phi> p \<in> elts \<bool>)"

text \<open>Denotation of a pwff:\<close>

definition is_pwff_denotation_function where
  [iff]: "is_pwff_denotation_function \<V> \<longleftrightarrow>
    (
      \<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow>
      (
        \<V> \<phi> T\<^bsub>o\<^esub> = \<^bold>T \<and>
        \<V> \<phi> F\<^bsub>o\<^esub> = \<^bold>F \<and>
        (\<forall>p. \<V> \<phi> (p\<^bsub>o\<^esub>) = \<phi> p) \<and>
        (\<forall>A. A \<in> pwffs \<longrightarrow> \<V> \<phi> (\<sim>\<^sup>\<Q> A) = \<sim> \<V> \<phi> A) \<and>
        (\<forall>A B. A \<in> pwffs \<and> B \<in> pwffs \<longrightarrow> \<V> \<phi> (A \<and>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<and> \<V> \<phi> B) \<and>
        (\<forall>A B. A \<in> pwffs \<and> B \<in> pwffs \<longrightarrow> \<V> \<phi> (A \<or>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<or> \<V> \<phi> B) \<and>
        (\<forall>A B. A \<in> pwffs \<and> B \<in> pwffs \<longrightarrow> \<V> \<phi> (A \<supset>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<supset> \<V> \<phi> B) \<and>
        (\<forall>A B. A \<in> pwffs \<and> B \<in> pwffs \<longrightarrow> \<V> \<phi> (A \<equiv>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<equiv> \<V> \<phi> B)
      )
    )"

lemma pwff_denotation_is_truth_value:
  assumes "A \<in> pwffs"
  and "is_tv_assignment \<phi>"
  and "is_pwff_denotation_function \<V>"
  shows "\<V> \<phi> A \<in> elts \<bool>"
using assms(1) proof induction
  case (neg_pwff A)
  then have "\<V> \<phi> (\<sim>\<^sup>\<Q> A) = \<sim> \<V> \<phi> A"
    using assms(2,3) by auto
  then show ?case
    using neg_pwff.IH by auto
next
  case (conj_pwff A B)
  then have "\<V> \<phi> (A \<and>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<and> \<V> \<phi> B"
    using assms(2,3) by auto
  then show ?case
    using conj_pwff.IH by auto
next
  case (disj_pwff A B)
  then have "\<V> \<phi> (A \<or>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<or> \<V> \<phi> B"
    using assms(2,3) by auto
  then show ?case
    using disj_pwff.IH by auto
next
  case (imp_pwff A B)
  then have "\<V> \<phi> (A \<supset>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<supset> \<V> \<phi> B"
    using assms(2,3) by blast
  then show ?case
    using imp_pwff.IH by auto
next
  case (eqv_pwff A B)
  then have "\<V> \<phi> (A \<equiv>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<equiv> \<V> \<phi> B"
    using assms(2,3) by blast
  then show ?case
    using eqv_pwff.IH by auto
qed (use assms(2,3) in auto)

lemma closed_pwff_is_meaningful_regardless_of_assignment:
  assumes "A \<in> pwffs"
  and "free_vars A = {}"
  and "is_tv_assignment \<phi>"
  and "is_tv_assignment \<psi>"
  and "is_pwff_denotation_function \<V>"
  shows "\<V> \<phi> A = \<V> \<psi> A"
using assms(1,2) proof induction
  case T_pwff
  have "\<V> \<phi> T\<^bsub>o\<^esub> = \<^bold>T"
    using assms(3,5) by blast
  also have "\<dots> = \<V> \<psi> T\<^bsub>o\<^esub>"
    using assms(4,5) by force
  finally show ?case .
next
  case F_pwff
  have "\<V> \<phi> F\<^bsub>o\<^esub> = \<^bold>F"
    using assms(3,5) by blast
  also have "\<dots> = \<V> \<psi> F\<^bsub>o\<^esub>"
    using assms(4,5) by force
  finally show ?case .
next
  case (var_pwff p) \<comment> \<open>impossible case\<close>
  then show ?case
    by simp
next
  case (neg_pwff A)
  from \<open>free_vars (\<sim>\<^sup>\<Q> A) = {}\<close> have "free_vars A = {}"
    by simp
  have "\<V> \<phi> (\<sim>\<^sup>\<Q> A) = \<sim> \<V> \<phi> A"
    using assms(3,5) and neg_pwff.hyps by auto
  also from \<open>free_vars A = {}\<close> have "\<dots> = \<sim> \<V> \<psi> A"
    using assms(3-5) and neg_pwff.IH by presburger
  also have "\<dots> = \<V> \<psi> (\<sim>\<^sup>\<Q> A)"
    using assms(4,5) and neg_pwff.hyps by simp
  finally show ?case .
next
  case (conj_pwff A B)
  from \<open>free_vars (A \<and>\<^sup>\<Q> B) = {}\<close> have "free_vars A = {}" and "free_vars B = {}"
    by simp_all
  have "\<V> \<phi> (A \<and>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<and> \<V> \<phi> B"
    using assms(3,5) and conj_pwff.hyps(1,2) by auto
  also from \<open>free_vars A = {}\<close> and \<open>free_vars B = {}\<close> have "\<dots> = \<V> \<psi> A \<^bold>\<and> \<V> \<psi> B"
    using conj_pwff.IH(1,2) by presburger
  also have "\<dots> = \<V> \<psi> (A \<and>\<^sup>\<Q> B)"
    using assms(4,5) and conj_pwff.hyps(1,2) by fastforce
  finally show ?case .
next
  case (disj_pwff A B)
  from \<open>free_vars (A \<or>\<^sup>\<Q> B) = {}\<close> have "free_vars A = {}" and "free_vars B = {}"
    by simp_all
  have "\<V> \<phi> (A \<or>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<or> \<V> \<phi> B"
    using assms(3,5) and disj_pwff.hyps(1,2) by auto
  also from \<open>free_vars A = {}\<close> and \<open>free_vars B = {}\<close> have "\<dots> = \<V> \<psi> A \<^bold>\<or> \<V> \<psi> B"
    using disj_pwff.IH(1,2) by presburger
  also have "\<dots> = \<V> \<psi> (A \<or>\<^sup>\<Q> B)"
    using assms(4,5) and disj_pwff.hyps(1,2) by fastforce
  finally show ?case .
next
  case (imp_pwff A B)
  from \<open>free_vars (A \<supset>\<^sup>\<Q> B) = {}\<close> have "free_vars A = {}" and "free_vars B = {}"
    by simp_all
  have "\<V> \<phi> (A \<supset>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<supset> \<V> \<phi> B"
    using assms(3,5) and imp_pwff.hyps(1,2) by auto
  also from \<open>free_vars A = {}\<close> and \<open>free_vars B = {}\<close> have "\<dots> = \<V> \<psi> A \<^bold>\<supset> \<V> \<psi> B"
    using imp_pwff.IH(1,2) by presburger
  also have "\<dots> = \<V> \<psi> (A \<supset>\<^sup>\<Q> B)"
    using assms(4,5) and imp_pwff.hyps(1,2) by fastforce
  finally show ?case .
next
  case (eqv_pwff A B)
  from \<open>free_vars (A \<equiv>\<^sup>\<Q> B) = {}\<close> have "free_vars A = {}" and "free_vars B = {}"
    by simp_all
  have "\<V> \<phi> (A \<equiv>\<^sup>\<Q> B) = \<V> \<phi> A \<^bold>\<equiv> \<V> \<phi> B"
    using assms(3,5) and eqv_pwff.hyps(1,2) by auto
  also from \<open>free_vars A = {}\<close> and \<open>free_vars B = {}\<close> have "\<dots> = \<V> \<psi> A \<^bold>\<equiv> \<V> \<psi> B"
    using eqv_pwff.IH(1,2) by presburger
  also have "\<dots> = \<V> \<psi> (A \<equiv>\<^sup>\<Q> B)"
    using assms(4,5) and eqv_pwff.hyps(1,2) by fastforce
  finally show ?case .
qed

inductive \<V>\<^sub>B_graph for \<phi> where
  \<V>\<^sub>B_graph_T: "\<V>\<^sub>B_graph \<phi> T\<^bsub>o\<^esub> \<^bold>T"
| \<V>\<^sub>B_graph_F: "\<V>\<^sub>B_graph \<phi> F\<^bsub>o\<^esub> \<^bold>F"
| \<V>\<^sub>B_graph_var: "\<V>\<^sub>B_graph \<phi> (p\<^bsub>o\<^esub>) (\<phi> p)"
| \<V>\<^sub>B_graph_neg: "\<V>\<^sub>B_graph \<phi> (\<sim>\<^sup>\<Q> A) (\<sim> b\<^sub>A)" if "\<V>\<^sub>B_graph \<phi> A b\<^sub>A"
| \<V>\<^sub>B_graph_conj: "\<V>\<^sub>B_graph \<phi> (A \<and>\<^sup>\<Q> B) (b\<^sub>A \<^bold>\<and> b\<^sub>B)" if "\<V>\<^sub>B_graph \<phi> A b\<^sub>A" and "\<V>\<^sub>B_graph \<phi> B b\<^sub>B"
| \<V>\<^sub>B_graph_disj: "\<V>\<^sub>B_graph \<phi> (A \<or>\<^sup>\<Q> B) (b\<^sub>A \<^bold>\<or> b\<^sub>B)" if "\<V>\<^sub>B_graph \<phi> A b\<^sub>A" and "\<V>\<^sub>B_graph \<phi> B b\<^sub>B"
| \<V>\<^sub>B_graph_imp: "\<V>\<^sub>B_graph \<phi> (A \<supset>\<^sup>\<Q> B) (b\<^sub>A \<^bold>\<supset> b\<^sub>B)" if "\<V>\<^sub>B_graph \<phi> A b\<^sub>A" and "\<V>\<^sub>B_graph \<phi> B b\<^sub>B"
| \<V>\<^sub>B_graph_eqv: "\<V>\<^sub>B_graph \<phi> (A \<equiv>\<^sup>\<Q> B) (b\<^sub>A \<^bold>\<equiv> b\<^sub>B)" if "\<V>\<^sub>B_graph \<phi> A b\<^sub>A" and "\<V>\<^sub>B_graph \<phi> B b\<^sub>B" and "A \<noteq> F\<^bsub>o\<^esub>"

lemmas [intro!] = \<V>\<^sub>B_graph.intros

lemma \<V>\<^sub>B_graph_denotation_is_truth_value [elim!]:
  assumes "\<V>\<^sub>B_graph \<phi> A b"
  and "is_tv_assignment \<phi>"
  shows "b \<in> elts \<bool>"
using assms proof induction
  case (\<V>\<^sub>B_graph_neg A b\<^sub>A)
  show ?case
    using \<V>\<^sub>B_graph_neg.IH[OF assms(2)] by force
next
  case (\<V>\<^sub>B_graph_conj A b\<^sub>A B b\<^sub>B)
  then show ?case
    using \<V>\<^sub>B_graph_conj.IH and assms(2) by force
next
  case (\<V>\<^sub>B_graph_disj A b\<^sub>A B b\<^sub>B)
  then show ?case
    using \<V>\<^sub>B_graph_disj.IH and assms(2) by force
next
  case (\<V>\<^sub>B_graph_imp A b\<^sub>A B b\<^sub>B)
  then show ?case
    using \<V>\<^sub>B_graph_imp.IH and assms(2) by force
next
  case (\<V>\<^sub>B_graph_eqv A b\<^sub>A B b\<^sub>B)
  then show ?case
    using \<V>\<^sub>B_graph_eqv.IH and assms(2) by force
qed simp_all

lemma \<V>\<^sub>B_graph_denotation_uniqueness:
  assumes "A \<in> pwffs"
  and "is_tv_assignment \<phi>"
  and "\<V>\<^sub>B_graph \<phi> A b" and "\<V>\<^sub>B_graph \<phi> A b'"
  shows "b = b'"
using assms(3,1,4) proof (induction arbitrary: b')
  case \<V>\<^sub>B_graph_T
  from \<open>\<V>\<^sub>B_graph \<phi> T\<^bsub>o\<^esub> b'\<close> show ?case
    by (cases rule: \<V>\<^sub>B_graph.cases) simp_all
next
  case \<V>\<^sub>B_graph_F
  from \<open>\<V>\<^sub>B_graph \<phi> F\<^bsub>o\<^esub> b'\<close> show ?case
    by (cases rule: \<V>\<^sub>B_graph.cases) simp_all
next
  case (\<V>\<^sub>B_graph_var p)
  from \<open>\<V>\<^sub>B_graph \<phi> (p\<^bsub>o\<^esub>) b'\<close> show ?case
    by (cases rule: \<V>\<^sub>B_graph.cases) simp_all
next
  case (\<V>\<^sub>B_graph_neg A b\<^sub>A)
  with \<open>\<V>\<^sub>B_graph \<phi> (\<sim>\<^sup>\<Q> A) b'\<close> have "\<V>\<^sub>B_graph \<phi> A (\<sim> b')"
  proof (cases rule: \<V>\<^sub>B_graph.cases)
    case (\<V>\<^sub>B_graph_neg A' b\<^sub>A)
    from \<open>\<sim>\<^sup>\<Q> A = \<sim>\<^sup>\<Q> A'\<close> have "A = A'"
      by simp
    with \<open>\<V>\<^sub>B_graph \<phi> A' b\<^sub>A\<close> have "\<V>\<^sub>B_graph \<phi> A b\<^sub>A"
      by simp
    moreover have "b\<^sub>A = \<sim> b'"
    proof -
      have "b\<^sub>A \<in> elts \<bool>"
        by (fact \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<V>\<^sub>B_graph_neg(3) assms(2)])
      moreover from \<open>b\<^sub>A \<in> elts \<bool>\<close> and \<V>\<^sub>B_graph_neg(2) have "\<sim> b' \<in> elts \<bool>"
        by fastforce
      ultimately show ?thesis
        using \<V>\<^sub>B_graph_neg(2) by fastforce
    qed
    ultimately show ?thesis
      by blast
  qed simp_all
  moreover from \<V>\<^sub>B_graph_neg.prems(1) have "A \<in> pwffs"
    by (force elim: pwffs.cases)
  moreover have "b\<^sub>A \<in> elts \<bool>" and "b' \<in> elts \<bool>" and "b\<^sub>A = \<sim> b'"
  proof -
    show "b\<^sub>A \<in> elts \<bool>"
      by (fact \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<open>\<V>\<^sub>B_graph \<phi> A b\<^sub>A\<close> assms(2)])
    show "b' \<in> elts \<bool>"
      by (fact \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<open>\<V>\<^sub>B_graph \<phi> (\<sim>\<^sup>\<Q> A) b'\<close> assms(2)])
    show "b\<^sub>A = \<sim> b'"
      by (fact \<V>\<^sub>B_graph_neg(2)[OF \<open>A \<in> pwffs\<close> \<open>\<V>\<^sub>B_graph \<phi> A (\<sim> b')\<close>])
  qed
  ultimately show ?case
    by force
next
  case (\<V>\<^sub>B_graph_conj A b\<^sub>A B b\<^sub>B)
  with \<open>\<V>\<^sub>B_graph \<phi> (A \<and>\<^sup>\<Q> B) b'\<close> obtain b\<^sub>A' and b\<^sub>B'
    where "b' = b\<^sub>A' \<^bold>\<and> b\<^sub>B'" and "\<V>\<^sub>B_graph \<phi> A b\<^sub>A'" and "\<V>\<^sub>B_graph \<phi> B b\<^sub>B'"
    by (cases rule: \<V>\<^sub>B_graph.cases) simp_all
  moreover have "A \<in> pwffs" and "B \<in> pwffs"
    using pwffs_from_conj_pwff[OF \<V>\<^sub>B_graph_conj.prems(1)] by blast+
  ultimately show ?case
    using \<V>\<^sub>B_graph_conj.IH and \<V>\<^sub>B_graph_conj.prems(2) by blast
next
  case (\<V>\<^sub>B_graph_disj A b\<^sub>A B b\<^sub>B)
  from \<open>\<V>\<^sub>B_graph \<phi> (A \<or>\<^sup>\<Q> B) b'\<close> obtain b\<^sub>A' and b\<^sub>B'
    where "b' = b\<^sub>A' \<^bold>\<or> b\<^sub>B'" and "\<V>\<^sub>B_graph \<phi> A b\<^sub>A'" and "\<V>\<^sub>B_graph \<phi> B b\<^sub>B'"
    by (cases rule: \<V>\<^sub>B_graph.cases) simp_all
  moreover have "A \<in> pwffs" and "B \<in> pwffs"
    using pwffs_from_disj_pwff[OF \<V>\<^sub>B_graph_disj.prems(1)] by blast+
  ultimately show ?case
    using \<V>\<^sub>B_graph_disj.IH and \<V>\<^sub>B_graph_disj.prems(2) by blast
next
  case (\<V>\<^sub>B_graph_imp A b\<^sub>A B b\<^sub>B)
  from \<open>\<V>\<^sub>B_graph \<phi> (A \<supset>\<^sup>\<Q> B) b'\<close> obtain b\<^sub>A' and b\<^sub>B'
    where "b' = b\<^sub>A' \<^bold>\<supset> b\<^sub>B'" and "\<V>\<^sub>B_graph \<phi> A b\<^sub>A'" and "\<V>\<^sub>B_graph \<phi> B b\<^sub>B'"
    by (cases rule: \<V>\<^sub>B_graph.cases) simp_all
  moreover have "A \<in> pwffs" and "B \<in> pwffs"
    using pwffs_from_imp_pwff[OF \<V>\<^sub>B_graph_imp.prems(1)] by blast+
  ultimately show ?case
    using \<V>\<^sub>B_graph_imp.IH and \<V>\<^sub>B_graph_imp.prems(2) by blast
next
  case (\<V>\<^sub>B_graph_eqv A b\<^sub>A B b\<^sub>B)
  with \<open>\<V>\<^sub>B_graph \<phi> (A \<equiv>\<^sup>\<Q> B) b'\<close> obtain b\<^sub>A' and b\<^sub>B'
    where "b' = b\<^sub>A' \<^bold>\<equiv> b\<^sub>B'" and "\<V>\<^sub>B_graph \<phi> A b\<^sub>A'" and "\<V>\<^sub>B_graph \<phi> B b\<^sub>B'"
    by (cases rule: \<V>\<^sub>B_graph.cases) simp_all
  moreover have "A \<in> pwffs" and "B \<in> pwffs"
    using pwffs_from_eqv_pwff[OF \<V>\<^sub>B_graph_eqv.prems(1)] by blast+
  ultimately show ?case
    using \<V>\<^sub>B_graph_eqv.IH and \<V>\<^sub>B_graph_eqv.prems(2) by blast
qed

lemma \<V>\<^sub>B_graph_denotation_existence:
  assumes "A \<in> pwffs"
  and "is_tv_assignment \<phi>"
  shows "\<exists>b. \<V>\<^sub>B_graph \<phi> A b"
using assms proof induction
  case (eqv_pwff A B)
  then obtain b\<^sub>A and b\<^sub>B where "\<V>\<^sub>B_graph \<phi> A b\<^sub>A" and "\<V>\<^sub>B_graph \<phi> B b\<^sub>B"
    by blast
  then show ?case
  proof (cases "A \<noteq> F\<^bsub>o\<^esub>")
    case True
    then show ?thesis
      using eqv_pwff.IH and eqv_pwff.prems by blast
  next
    case False
    then have "A = F\<^bsub>o\<^esub>"
      by blast
    then show ?thesis
      using \<V>\<^sub>B_graph_neg[OF \<open>\<V>\<^sub>B_graph \<phi> B b\<^sub>B\<close>] by auto
  qed
qed blast+

lemma \<V>\<^sub>B_graph_is_functional:
  assumes "A \<in> pwffs"
  and "is_tv_assignment \<phi>"
  shows "\<exists>!b. \<V>\<^sub>B_graph \<phi> A b"
  using assms and \<V>\<^sub>B_graph_denotation_existence and \<V>\<^sub>B_graph_denotation_uniqueness by blast

definition \<V>\<^sub>B :: "(nat \<Rightarrow> V) \<Rightarrow> form \<Rightarrow> V" where
  [simp]: "\<V>\<^sub>B \<phi> A = (THE b. \<V>\<^sub>B_graph \<phi> A b)"

lemma \<V>\<^sub>B_equality:
  assumes "A \<in> pwffs"
  and "is_tv_assignment \<phi>"
  and "\<V>\<^sub>B_graph \<phi> A b"
  shows "\<V>\<^sub>B \<phi> A = b"
  unfolding \<V>\<^sub>B_def using assms using \<V>\<^sub>B_graph_denotation_uniqueness by blast

lemma \<V>\<^sub>B_graph_\<V>\<^sub>B:
  assumes "A \<in> pwffs"
  and "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B_graph \<phi> A (\<V>\<^sub>B \<phi> A)"
  using \<V>\<^sub>B_equality[OF assms] and \<V>\<^sub>B_graph_is_functional[OF assms] by blast

named_theorems \<V>\<^sub>B_simps

lemma \<V>\<^sub>B_T [\<V>\<^sub>B_simps]:
  assumes "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B \<phi> T\<^bsub>o\<^esub> = \<^bold>T"
  by (rule \<V>\<^sub>B_equality[OF T_pwff assms], intro \<V>\<^sub>B_graph_T)

lemma \<V>\<^sub>B_F [\<V>\<^sub>B_simps]:
  assumes "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B \<phi> F\<^bsub>o\<^esub> = \<^bold>F"
  by (rule \<V>\<^sub>B_equality[OF F_pwff assms], intro \<V>\<^sub>B_graph_F)

lemma \<V>\<^sub>B_var [\<V>\<^sub>B_simps]:
  assumes "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B \<phi> (p\<^bsub>o\<^esub>) = \<phi> p"
  by (rule \<V>\<^sub>B_equality[OF var_pwff assms], intro \<V>\<^sub>B_graph_var)

lemma \<V>\<^sub>B_neg [\<V>\<^sub>B_simps]:
  assumes "A \<in> pwffs"
  and "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B \<phi> (\<sim>\<^sup>\<Q> A) = \<sim> \<V>\<^sub>B \<phi> A"
  by (rule \<V>\<^sub>B_equality[OF neg_pwff[OF assms(1)] assms(2)], intro \<V>\<^sub>B_graph_neg \<V>\<^sub>B_graph_\<V>\<^sub>B[OF assms])

lemma \<V>\<^sub>B_disj [\<V>\<^sub>B_simps]:
  assumes "A \<in> pwffs" and "B \<in> pwffs"
  and "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B \<phi> (A \<or>\<^sup>\<Q> B) = \<V>\<^sub>B \<phi> A \<^bold>\<or> \<V>\<^sub>B \<phi> B"
proof -
  from assms(1,3) have "\<V>\<^sub>B_graph \<phi> A (\<V>\<^sub>B \<phi> A)"
    by (intro \<V>\<^sub>B_graph_\<V>\<^sub>B)
  moreover from assms(2,3) have "\<V>\<^sub>B_graph \<phi> B (\<V>\<^sub>B \<phi> B)"
    by (intro \<V>\<^sub>B_graph_\<V>\<^sub>B)
  ultimately have "\<V>\<^sub>B_graph \<phi> (A \<or>\<^sup>\<Q> B) (\<V>\<^sub>B \<phi> A \<^bold>\<or> \<V>\<^sub>B \<phi> B)"
    by (intro \<V>\<^sub>B_graph_disj)
  with assms show ?thesis
    using disj_pwff by (intro \<V>\<^sub>B_equality)
qed

lemma \<V>\<^sub>B_conj [\<V>\<^sub>B_simps]:
  assumes "A \<in> pwffs" and "B \<in> pwffs"
  and "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B \<phi> (A \<and>\<^sup>\<Q> B) = \<V>\<^sub>B \<phi> A \<^bold>\<and> \<V>\<^sub>B \<phi> B"
proof -
  from assms(1,3) have "\<V>\<^sub>B_graph \<phi> A (\<V>\<^sub>B \<phi> A)"
    by (intro \<V>\<^sub>B_graph_\<V>\<^sub>B)
  moreover from assms(2,3) have "\<V>\<^sub>B_graph \<phi> B (\<V>\<^sub>B \<phi> B)"
    by (intro \<V>\<^sub>B_graph_\<V>\<^sub>B)
  ultimately have "\<V>\<^sub>B_graph \<phi> (A \<and>\<^sup>\<Q> B) (\<V>\<^sub>B \<phi> A \<^bold>\<and> \<V>\<^sub>B \<phi> B)"
    by (intro \<V>\<^sub>B_graph_conj)
  with assms show ?thesis
    using conj_pwff by (intro \<V>\<^sub>B_equality)
qed

lemma \<V>\<^sub>B_imp [\<V>\<^sub>B_simps]:
  assumes "A \<in> pwffs" and "B \<in> pwffs"
  and "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B \<phi> (A \<supset>\<^sup>\<Q> B) = \<V>\<^sub>B \<phi> A \<^bold>\<supset> \<V>\<^sub>B \<phi> B"
proof -
  from assms(1,3) have "\<V>\<^sub>B_graph \<phi> A (\<V>\<^sub>B \<phi> A)"
    by (intro \<V>\<^sub>B_graph_\<V>\<^sub>B)
  moreover from assms(2,3) have "\<V>\<^sub>B_graph \<phi> B (\<V>\<^sub>B \<phi> B)"
    by (intro \<V>\<^sub>B_graph_\<V>\<^sub>B)
  ultimately have "\<V>\<^sub>B_graph \<phi> (A \<supset>\<^sup>\<Q> B) (\<V>\<^sub>B \<phi> A \<^bold>\<supset> \<V>\<^sub>B \<phi> B)"
    by (intro \<V>\<^sub>B_graph_imp)
  with assms show ?thesis
    using imp_pwff by (intro \<V>\<^sub>B_equality)
qed

lemma \<V>\<^sub>B_eqv [\<V>\<^sub>B_simps]:
  assumes "A \<in> pwffs" and "B \<in> pwffs"
  and "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B \<phi> (A \<equiv>\<^sup>\<Q> B) = \<V>\<^sub>B \<phi> A \<^bold>\<equiv> \<V>\<^sub>B \<phi> B"
proof (cases "A = F\<^bsub>o\<^esub>")
  case True
  then show ?thesis
    using \<V>\<^sub>B_F[OF assms(3)] and \<V>\<^sub>B_neg[OF assms(2,3)] by force
next
  case False
  from assms(1,3) have "\<V>\<^sub>B_graph \<phi> A (\<V>\<^sub>B \<phi> A)"
    by (intro \<V>\<^sub>B_graph_\<V>\<^sub>B)
  moreover from assms(2,3) have "\<V>\<^sub>B_graph \<phi> B (\<V>\<^sub>B \<phi> B)"
    by (intro \<V>\<^sub>B_graph_\<V>\<^sub>B)
  ultimately have "\<V>\<^sub>B_graph \<phi> (A \<equiv>\<^sup>\<Q> B) (\<V>\<^sub>B \<phi> A \<^bold>\<equiv> \<V>\<^sub>B \<phi> B)"
    using False by (intro \<V>\<^sub>B_graph_eqv)
  with assms show ?thesis
    using eqv_pwff by (intro \<V>\<^sub>B_equality)
qed

declare pwffs.intros [\<V>\<^sub>B_simps]

lemma pwff_denotation_function_existence:
  shows "is_pwff_denotation_function \<V>\<^sub>B"
  using \<V>\<^sub>B_simps by simp

text \<open>Tautologies:\<close>

definition is_tautology :: "form \<Rightarrow> bool" where
  [iff]: "is_tautology A \<longleftrightarrow> A \<in> pwffs \<and> (\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> A = \<^bold>T)"

lemma tautology_is_wffo:
  assumes "is_tautology A"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
  using assms and pwffs_subset_of_wffso by blast

lemma propositional_implication_reflexivity_is_tautology:
  shows "is_tautology (p\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> p\<^bsub>o\<^esub>)"
  using \<V>\<^sub>B_simps by simp

lemma propositional_principle_of_simplification_is_tautology:
  shows "is_tautology (p\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (r\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> p\<^bsub>o\<^esub>))"
  using \<V>\<^sub>B_simps by simp

lemma closed_pwff_denotation_uniqueness:
  assumes "A \<in> pwffs" and "free_vars A = {}"
  obtains b where "\<forall>\<phi>. is_tv_assignment \<phi> \<longrightarrow> \<V>\<^sub>B \<phi> A = b"
  using assms
  by (meson closed_pwff_is_meaningful_regardless_of_assignment pwff_denotation_function_existence)

lemma pwff_substitution_simps:
  shows "\<^bold>S {(p, o) \<Zinj> A} T\<^bsub>o\<^esub> = T\<^bsub>o\<^esub>"
  and "\<^bold>S {(p, o) \<Zinj> A} F\<^bsub>o\<^esub> = F\<^bsub>o\<^esub>"
  and "\<^bold>S {(p, o) \<Zinj> A} (p'\<^bsub>o\<^esub>) = (if p = p' then A else (p'\<^bsub>o\<^esub>))"
  and "\<^bold>S {(p, o) \<Zinj> A} (\<sim>\<^sup>\<Q> B) = \<sim>\<^sup>\<Q> (\<^bold>S {(p, o) \<Zinj> A} B)"
  and "\<^bold>S {(p, o) \<Zinj> A} (B \<and>\<^sup>\<Q> C) = (\<^bold>S {(p, o) \<Zinj> A} B) \<and>\<^sup>\<Q> (\<^bold>S {(p, o) \<Zinj> A} C)"
  and "\<^bold>S {(p, o) \<Zinj> A} (B \<or>\<^sup>\<Q> C) = (\<^bold>S {(p, o) \<Zinj> A} B) \<or>\<^sup>\<Q> (\<^bold>S {(p, o) \<Zinj> A} C)"
  and "\<^bold>S {(p, o) \<Zinj> A} (B \<supset>\<^sup>\<Q> C) = (\<^bold>S {(p, o) \<Zinj> A} B) \<supset>\<^sup>\<Q> (\<^bold>S {(p, o) \<Zinj> A} C)"
  and "\<^bold>S {(p, o) \<Zinj> A} (B \<equiv>\<^sup>\<Q> C) = (\<^bold>S {(p, o) \<Zinj> A} B) \<equiv>\<^sup>\<Q> (\<^bold>S {(p, o) \<Zinj> A} C)"
  by simp_all

lemma pwff_substitution_in_pwffs:
  assumes "A \<in> pwffs" and "B \<in> pwffs"
  shows "\<^bold>S {(p, o) \<Zinj> A} B \<in> pwffs"
using assms(2) proof induction
  case T_pwff
  then show ?case
    using pwffs.T_pwff by simp
next
  case F_pwff
  then show ?case
    using pwffs.F_pwff by simp
next
  case (var_pwff p)
  from assms(1) show ?case
    using pwffs.var_pwff by simp
next
  case (neg_pwff A)
  then show ?case
    using pwff_substitution_simps(4) and pwffs.neg_pwff by simp
next
  case (conj_pwff A B)
  then show ?case
    using pwff_substitution_simps(5) and pwffs.conj_pwff by simp
next
  case (disj_pwff A B)
  then show ?case
    using pwff_substitution_simps(6) and pwffs.disj_pwff by simp
next
  case (imp_pwff A B)
  then show ?case
    using pwff_substitution_simps(7) and pwffs.imp_pwff by simp
next
  case (eqv_pwff A B)
  then show ?case
    using pwff_substitution_simps(8) and pwffs.eqv_pwff by simp
qed

lemma pwff_substitution_denotation:
  assumes "A \<in> pwffs" and "B \<in> pwffs"
  and "is_tv_assignment \<phi>"
  shows "\<V>\<^sub>B \<phi> (\<^bold>S {(p, o) \<Zinj> A} B) = \<V>\<^sub>B (\<phi>(p := \<V>\<^sub>B \<phi> A)) B"
proof -
  from assms(1,3) have "is_tv_assignment (\<phi>(p := \<V>\<^sub>B \<phi> A))"
    using \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<V>\<^sub>B_graph_\<V>\<^sub>B] by simp
  with assms(2,1,3) show ?thesis
    using \<V>\<^sub>B_simps and pwff_substitution_in_pwffs by induction auto
qed

lemma pwff_substitution_tautology_preservation:
  assumes "is_tautology B" and "A \<in> pwffs"
  and "(p, o) \<in> free_vars B"
  shows "is_tautology (\<^bold>S {(p, o) \<Zinj> A} B)"
proof (safe, fold is_tv_assignment_def)
  from assms(1,2) show "\<^bold>S {(p, o) \<Zinj> A} B \<in> pwffs"
    using pwff_substitution_in_pwffs by blast
next
  fix \<phi>
  assume "is_tv_assignment \<phi>"
  with assms(1,2) have "\<V>\<^sub>B \<phi> (\<^bold>S {(p, o) \<Zinj> A} B) = \<V>\<^sub>B (\<phi>(p := \<V>\<^sub>B \<phi> A)) B"
    using pwff_substitution_denotation by blast
  moreover from \<open>is_tv_assignment \<phi>\<close> and assms(2) have "is_tv_assignment (\<phi>(p := \<V>\<^sub>B \<phi> A))"
    using \<V>\<^sub>B_graph_denotation_is_truth_value[OF \<V>\<^sub>B_graph_\<V>\<^sub>B] by simp
  with assms(1) have "\<V>\<^sub>B (\<phi>(p := \<V>\<^sub>B \<phi> A)) B = \<^bold>T"
    by fastforce
  ultimately show "\<V>\<^sub>B \<phi> \<^bold>S {(p, o) \<Zinj> A} B = \<^bold>T"
    by (simp only:)
qed

lemma closed_pwff_substitution_free_vars:
  assumes "A \<in> pwffs" and "B \<in> pwffs"
  and "free_vars A = {}"
  and "(p, o) \<in> free_vars B"
  shows "free_vars (\<^bold>S {(p, o) \<Zinj> A} B) = free_vars B - {(p, o)}" (is \<open>free_vars (\<^bold>S ?\<theta> B) = _\<close>)
using assms(2,4) proof induction
  case (conj_pwff C D)
  have "free_vars (\<^bold>S ?\<theta> (C \<and>\<^sup>\<Q> D)) = free_vars ((\<^bold>S ?\<theta> C) \<and>\<^sup>\<Q> (\<^bold>S ?\<theta> D))"
    by simp
  also have "\<dots> = free_vars (\<^bold>S ?\<theta> C) \<union> free_vars (\<^bold>S ?\<theta> D)"
    by (fact conj_fv)
  finally have *: "free_vars (\<^bold>S ?\<theta> (C \<and>\<^sup>\<Q> D)) = free_vars (\<^bold>S ?\<theta> C) \<union> free_vars (\<^bold>S ?\<theta> D)" .
  from conj_pwff.prems consider
    (a) "(p, o) \<in> free_vars C" and "(p, o) \<in> free_vars D"
  | (b) "(p, o) \<in> free_vars C" and "(p, o) \<notin> free_vars D"
  | (c) "(p, o) \<notin> free_vars C" and "(p, o) \<in> free_vars D"
    by auto
  from this and * and conj_pwff.IH show ?case
    using free_var_singleton_substitution_neutrality by cases auto
next
  case (disj_pwff C D)
  have "free_vars (\<^bold>S ?\<theta> (C \<or>\<^sup>\<Q> D)) = free_vars ((\<^bold>S ?\<theta> C) \<or>\<^sup>\<Q> (\<^bold>S ?\<theta> D))"
    by simp
  also have "\<dots> = free_vars (\<^bold>S ?\<theta> C) \<union> free_vars (\<^bold>S ?\<theta> D)"
    by (fact disj_fv)
  finally have *: "free_vars (\<^bold>S ?\<theta> (C \<or>\<^sup>\<Q> D)) = free_vars (\<^bold>S ?\<theta> C) \<union> free_vars (\<^bold>S ?\<theta> D)" .
  from disj_pwff.prems consider
    (a) "(p, o) \<in> free_vars C" and "(p, o) \<in> free_vars D"
  | (b) "(p, o) \<in> free_vars C" and "(p, o) \<notin> free_vars D"
  | (c) "(p, o) \<notin> free_vars C" and "(p, o) \<in> free_vars D"
    by auto
  from this and * and disj_pwff.IH show ?case
    using free_var_singleton_substitution_neutrality by cases auto
next
  case (imp_pwff C D)
  have "free_vars (\<^bold>S ?\<theta> (C \<supset>\<^sup>\<Q> D)) = free_vars ((\<^bold>S ?\<theta> C) \<supset>\<^sup>\<Q> (\<^bold>S ?\<theta> D))"
    by simp
  also have "\<dots> = free_vars (\<^bold>S ?\<theta> C) \<union> free_vars (\<^bold>S ?\<theta> D)"
    by (fact imp_fv)
  finally have *: "free_vars (\<^bold>S ?\<theta> (C \<supset>\<^sup>\<Q> D)) = free_vars (\<^bold>S ?\<theta> C) \<union> free_vars (\<^bold>S ?\<theta> D)" .
  from imp_pwff.prems consider
    (a) "(p, o) \<in> free_vars C" and "(p, o) \<in> free_vars D"
  | (b) "(p, o) \<in> free_vars C" and "(p, o) \<notin> free_vars D"
  | (c) "(p, o) \<notin> free_vars C" and "(p, o) \<in> free_vars D"
    by auto
  from this and * and imp_pwff.IH show ?case
    using free_var_singleton_substitution_neutrality by cases auto
next
  case (eqv_pwff C D)
  have "free_vars (\<^bold>S ?\<theta> (C \<equiv>\<^sup>\<Q> D)) = free_vars ((\<^bold>S ?\<theta> C) \<equiv>\<^sup>\<Q> (\<^bold>S ?\<theta> D))"
    by simp
  also have "\<dots> = free_vars (\<^bold>S ?\<theta> C) \<union> free_vars (\<^bold>S ?\<theta> D)"
    by (fact eqv_fv)
  finally have *: "free_vars (\<^bold>S ?\<theta> (C \<equiv>\<^sup>\<Q> D)) = free_vars (\<^bold>S ?\<theta> C) \<union> free_vars (\<^bold>S ?\<theta> D)" .
  from eqv_pwff.prems consider
    (a) "(p, o) \<in> free_vars C" and "(p, o) \<in> free_vars D"
  | (b) "(p, o) \<in> free_vars C" and "(p, o) \<notin> free_vars D"
  | (c) "(p, o) \<notin> free_vars C" and "(p, o) \<in> free_vars D"
    by auto
  from this and * and eqv_pwff.IH show ?case
    using free_var_singleton_substitution_neutrality by cases auto
qed (use assms(3) in \<open>force+\<close>)

text \<open>Substitution in a pwff:\<close>

definition is_pwff_substitution where
  [iff]: "is_pwff_substitution \<theta> \<longleftrightarrow> is_substitution \<theta> \<and> (\<forall>(x, \<alpha>) \<in> fmdom' \<theta>. \<alpha> = o)"

text \<open>Tautologous pwff:\<close>

definition is_tautologous :: "form \<Rightarrow> bool" where
  [iff]: "is_tautologous B \<longleftrightarrow> (\<exists>\<theta> A. is_tautology A \<and> is_pwff_substitution \<theta> \<and> B = \<^bold>S \<theta> A)"

lemma tautologous_is_wffo:
  assumes "is_tautologous A"
  shows "A \<in> wffs\<^bsub>o\<^esub>"
  using assms and substitution_preserves_typing and tautology_is_wffo by blast

lemma implication_reflexivity_is_tautologous:
  assumes "A \<in> wffs\<^bsub>o\<^esub>"
  shows "is_tautologous (A \<supset>\<^sup>\<Q> A)"
proof -
  let ?\<theta> = "{(\<xx>, o) \<Zinj> A}"
  have "is_tautology (\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>)"
    by (fact propositional_implication_reflexivity_is_tautology)
  moreover have "is_pwff_substitution ?\<theta>"
    using assms by auto
  moreover have "A \<supset>\<^sup>\<Q> A = \<^bold>S ?\<theta> (\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>)"
    by simp
  ultimately show ?thesis
    by blast
qed

lemma principle_of_simplification_is_tautologous:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "is_tautologous (A \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> A))"
proof -
  let ?\<theta> = "{(\<xx>, o) \<Zinj> A, (\<yy>, o) \<Zinj> B}"
  have "is_tautology (\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (\<yy>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>))"
    by (fact propositional_principle_of_simplification_is_tautology)
  moreover have "is_pwff_substitution ?\<theta>"
    using assms by auto
  moreover have "A \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> A) = \<^bold>S ?\<theta> (\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> (\<yy>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>))"
    by simp
  ultimately show ?thesis
    by blast
qed

lemma pseudo_modus_tollens_is_tautologous:
  assumes "A \<in> wffs\<^bsub>o\<^esub>" and "B \<in> wffs\<^bsub>o\<^esub>"
  shows "is_tautologous ((A \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> A))"
proof -
  let ?\<theta> = "{(\<xx>, o) \<Zinj> A, (\<yy>, o) \<Zinj> B}"
  have "is_tautology ((\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> (\<yy>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>))"
    using \<V>\<^sub>B_simps by (safe, fold is_tv_assignment_def, simp only:) simp
  moreover have "is_pwff_substitution ?\<theta>"
    using assms by auto
  moreover have "(A \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> B) \<supset>\<^sup>\<Q> (B \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> A) = \<^bold>S ?\<theta> ((\<xx>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<yy>\<^bsub>o\<^esub>) \<supset>\<^sup>\<Q> (\<yy>\<^bsub>o\<^esub> \<supset>\<^sup>\<Q> \<sim>\<^sup>\<Q> \<xx>\<^bsub>o\<^esub>))"
    by simp
  ultimately show ?thesis
    by blast
qed

end
