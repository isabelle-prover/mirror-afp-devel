(*<*)
theory Stability
imports
  Galois
  Lifted_Predicates
begin

(*>*)
section\<open> Stability \label{sec:stability} \<close>

text\<open>

The essence of rely/guarantee reasoning is that sequential assertions must be \<^emph>\<open>stable\<close> with respect
to interfering transitions as expressed in a \<^emph>\<open>rely\<close> relation. Formally an assertion \<open>P\<close> is stable if it becomes
no less true for each transition in the rely \<open>r\<close>. This is essentially monotonicity, or that the extension of \<open>P\<close>
is \<open>r\<close>-closed.

References:
 \<^item> \<^citet>\<open>\<open>\S3.1.3\<close> in "Vafeiadis:2008"\<close> has a def for stability in terms of separation logic

\<close>

definition stable :: "'a rel \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "stable r P = monotone (\<lambda>x y. (x, y) \<in> r) (\<le>) P"

setup \<open>Sign.mandatory_path "stable"\<close>

named_theorems intro "stability intro rules"

lemma singleton_conv:
  shows "stable {(s, s')} P \<longleftrightarrow> (P s \<longrightarrow> P s')"
by (simp add: stable_def monotone_def le_bool_def)

lemma closed:
  shows "stable r P \<longleftrightarrow> r `` Collect P \<subseteq> Collect P"
unfolding stable_def monotone_def le_bool_def by auto

lemma rtrancl_conv:
  shows "stable (r\<^sup>*) = stable r"
by (auto simp: stable_def monotone_def le_bool_def fun_eq_iff elim!: rtrancl_induct)

lemma reflcl_conv:
  shows "stable (r\<^sup>=) = stable r"
unfolding stable_def monotone_def by simp

lemma empty[stable.intro]:
  shows "stable {} P"
unfolding stable_def by simp

lemma [stable.intro]:
  shows Id: "stable Id P"
    and Id_fst: "\<And>P. stable (Id \<times>\<^sub>R A) (\<lambda>s. P (fst s))"
    and Id_fst_fst_snd: "\<And>P. stable (Id \<times>\<^sub>R Id \<times>\<^sub>R A) (\<lambda>s. P (fst s) (fst (snd s)))"
by (simp_all add: stable_def monotone_def)

lemma UNIV:
  shows "stable UNIV P \<longleftrightarrow> (\<exists>c. P = \<langle>c\<rangle>)"
unfolding stable_def monotone_def le_bool_def by simp meson

lemma antimono_rel:
  shows "antimono (\<lambda>r. stable r P)"
unfolding stable_def monotone_def using subset_iff by (fastforce intro: antimonoI)

lemmas strengthen_rel[strg] = st_ord_antimono[OF stable.antimono_rel, unfolded le_bool_def]

lemma infI:
  assumes "stable r P"
  shows infI1: "stable (r \<inter> s) P"
    and infI2: "stable (s \<inter> r) P"
using assms unfolding stable_def monotone_def by simp_all

lemma UNION_conv:
  shows "stable (\<Union>x\<in>X. r x) P \<longleftrightarrow> (\<forall>x\<in>X. stable (r x) P)"
unfolding stable_def monotone_def by blast

lemmas UNIONI[stable.intro] = iffD2[OF stable.UNION_conv, rule_format]

lemma Union_conv:
  shows "stable (\<Union>X) P \<longleftrightarrow> (\<forall>x\<in>X. stable x P)"
unfolding stable_def monotone_def by blast

lemma union_conv:
  shows "stable (r \<union> s) P \<longleftrightarrow> stable r P \<and> stable s P"
unfolding stable_def monotone_def by blast

lemmas UnionI[stable.intro] = iffD2[OF stable.Union_conv, rule_format]
lemmas unionI[stable.intro] = iffD2[OF stable.union_conv, rule_format, unfolded conj_explode]


paragraph\<open> Properties of \<^const>\<open>stable\<close> with respect to the predicate \<close>

lemma const[stable.intro]:
  shows "stable r \<langle>c\<rangle>"
    and "stable r \<bottom>"
    and "stable r \<top>"
by (simp_all add: stable_def monotone_def)

lemma conjI[stable.intro]:
  assumes "stable r P"
  assumes "stable r Q"
  shows "stable r (P \<^bold>\<and> Q)"
using assms by (simp add: stable_def)

lemma disjI[stable.intro]:
  assumes "stable r P"
  assumes "stable r Q"
  shows "stable r (P \<^bold>\<or> Q)"
using assms by (simp add: stable_def monotone_def le_bool_def)

lemma implies_constI[stable.intro]:
  assumes "P \<Longrightarrow> stable r Q"
  shows "stable r (\<lambda>s. P \<longrightarrow> Q s)"
using assms by (auto simp: stable_def monotone_def le_bool_def)

lemma allI[stable.intro]:
  assumes "\<And>x. stable r (P x)"
  shows "stable r (\<^bold>\<forall>x. P x)"
using assms by (simp add: stable_def monotone_def le_bool_def)

lemma ballI[stable.intro]:
  assumes "\<And>x. x \<in> X \<Longrightarrow> stable r (P x)"
  shows "stable r (\<lambda>s. \<forall>x\<in>X. P x s)"
using assms by (simp add: stable_def monotone_def le_bool_def)

lemma stable_relprod_fstI[stable.intro]:
  assumes "stable r P"
  shows "stable (r \<times>\<^sub>R s) (\<lambda>s. P (fst s))"
using assms by (clarsimp simp: stable_def monotone_def)

lemma stable_relprod_sndI[stable.intro]:
  assumes "stable s P"
  shows "stable (r \<times>\<^sub>R s) (\<lambda>s. P (snd s))"
using assms by (clarsimp simp: stable_def monotone_def)

lemma local_only: \<comment>\<open> for predicates that are insensitive to the shared state \<close>
  assumes "\<And>ls s s'. P (ls, s) \<longleftrightarrow> P (ls, s')"
  shows "stable (Id \<times>\<^sub>R UNIV) P"
using assms by (fastforce simp: stable_def monotone_def le_bool_def)

lemma Id_on_proj:
  assumes "\<And>v. stable Id\<^bsub>f\<^esub> (\<lambda>s. P v s)"
  shows "stable Id\<^bsub>f\<^esub> (\<lambda>s. P (f s) s)"
using assms unfolding stable_def by (rule monotone_Id_on_proj)

lemma if_const_conv:
  shows "stable r (if c then P else Q) \<longleftrightarrow> stable r (\<lambda>s. c \<longrightarrow> P s) \<and> stable r (\<lambda>s. \<not>c \<longrightarrow> Q s)"
by (simp add: stable_def)

lemma ifI[stable.intro]:
  assumes "stable r (\<lambda>s. c s \<longrightarrow> P s)"
  assumes "stable r (\<lambda>s. \<not>c s \<longrightarrow> Q s)"
  shows "stable r (\<lambda>s. if c s then P s else Q s)"
using assms by (simp add: stable.intro)

lemma ifI2[stable.intro]:
  assumes "stable r (\<lambda>s. c s \<longrightarrow> P s s)"
  assumes "stable r (\<lambda>s. \<not>c s \<longrightarrow> Q s s)"
  shows "stable r (\<lambda>s. (if c s then P s else Q s) s)"
using assms by (simp add: stable.intro)

lemma case_optionI[stable.intro]:
  assumes "stable r (\<lambda>s. opt s = None \<longrightarrow> none s)"
  assumes "\<And>v. stable r (\<lambda>s. opt s = Some v \<longrightarrow> some v s)"
  shows "stable r (\<lambda>s. case opt s of None \<Rightarrow> none s | Some v \<Rightarrow> some v s)"
using assms by (simp add: stable.intro split: option.split)

lemma case_optionI2[stable.intro]:
  assumes "opt = None \<Longrightarrow> stable r none"
  assumes "\<And>v. opt = Some v \<Longrightarrow> stable r (some v)"
  shows "stable r (case opt of None \<Rightarrow> none | Some v \<Rightarrow> some v)"
using assms by (simp add: stable.intro split: option.split)

text\<open> In practice the following rules are often too weak \<close>

lemma impliesI:
  assumes "stable r (\<^bold>\<not>P)"
  assumes "stable r Q"
  shows "stable r (P \<^bold>\<longrightarrow> Q)"
using assms by (auto simp: stable_def monotone_def le_bool_def)

lemma exI:
  assumes "\<And>x. stable r (P x)"
  shows "stable r (\<^bold>\<exists>x. P x)"
using assms by (auto simp: stable_def monotone_def le_bool_def)

lemma bexI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> stable r (P x)"
  shows "stable r (\<lambda>s. \<exists>x\<in>X. P x s)"
using assms by (auto simp: stable_def monotone_def le_bool_def)

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
