section \<open>Language and Semantics\<close>

text \<open>In this file, we formalize the programming language from section III, and the extended states
and semantics from section IV of the paper~\cite{HyperHoareLogic}. We also prove the useful properties described by Lemma 1.\<close>

theory Language
  imports Main
begin

subsection Language

text \<open>Definition 1\<close>

type_synonym ('var, 'val) pstate = "'var \<Rightarrow> 'val"

text \<open>Definition 2\<close>

type_synonym ('var, 'val) bexp = "('var, 'val) pstate \<Rightarrow> bool"
type_synonym ('var, 'val) exp = "('var, 'val) pstate \<Rightarrow> 'val"


datatype ('var, 'val) stmt = 
  Assign 'var "('var, 'val) exp"
  | Seq "('var, 'val) stmt" "('var, 'val) stmt"
  | If "('var, 'val) stmt" "('var, 'val) stmt"
  | Skip
  | Havoc 'var
  | Assume "('var, 'val) bexp"
  | While "('var, 'val) stmt"

subsection Semantics

text \<open>Figure 2\<close>

inductive single_sem :: "('var, 'val) stmt \<Rightarrow> ('var, 'val) pstate \<Rightarrow> ('var, 'val) pstate \<Rightarrow> bool"
  ("\<langle>_, _\<rangle> \<rightarrow> _" [51,0] 81)
  where
  SemSkip: "\<langle>Skip, \<sigma>\<rangle> \<rightarrow> \<sigma>"
| SemAssign: "\<langle>Assign var e, \<sigma>\<rangle> \<rightarrow> \<sigma>(var := (e \<sigma>))"
| SemSeq: "\<lbrakk> \<langle>C1, \<sigma>\<rangle> \<rightarrow> \<sigma>1; \<langle>C2, \<sigma>1\<rangle> \<rightarrow> \<sigma>2 \<rbrakk> \<Longrightarrow> \<langle>Seq C1 C2, \<sigma>\<rangle> \<rightarrow> \<sigma>2"
| SemIf1: "\<langle>C1, \<sigma>\<rangle> \<rightarrow> \<sigma>1 \<Longrightarrow> \<langle>If C1 C2, \<sigma>\<rangle> \<rightarrow> \<sigma>1"
| SemIf2: "\<langle>C2, \<sigma>\<rangle> \<rightarrow> \<sigma>2 \<Longrightarrow> \<langle>If C1 C2, \<sigma>\<rangle> \<rightarrow> \<sigma>2"
| SemHavoc: "\<langle>Havoc var, \<sigma>\<rangle> \<rightarrow> \<sigma>(var := v)"
| SemAssume: "b \<sigma> \<Longrightarrow> \<langle>Assume b, \<sigma>\<rangle> \<rightarrow> \<sigma>"
| SemWhileIter: "\<lbrakk> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>' ; \<langle>While C, \<sigma>'\<rangle> \<rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> \<langle>While C, \<sigma>\<rangle> \<rightarrow> \<sigma>''"
| SemWhileExit: "\<langle>While C, \<sigma>\<rangle> \<rightarrow> \<sigma>"

inductive_cases single_sem_Seq_elim[elim!]: "\<langle>Seq C1 C2, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
inductive_cases single_sem_Skip_elim[elim!]: "\<langle>Skip, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
inductive_cases single_sem_While_elim: "\<langle>While C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
inductive_cases single_sem_If_elim[elim!]: "\<langle>If C1 C2, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
inductive_cases single_sem_Assume_elim[elim!]: "\<langle>Assume b, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
inductive_cases single_sem_Assign_elim[elim!]: "\<langle>Assign x e, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
inductive_cases single_sem_Havoc_elim[elim!]: "\<langle>Havoc x, \<sigma>\<rangle> \<rightarrow> \<sigma>'"


section \<open>Extended States and Extended Semantics\<close>

text \<open>Definition 3\<close>
type_synonym ('lvar, 'lval, 'pvar, 'pval) state = "('lvar \<Rightarrow> 'lval) \<times> ('pvar, 'pval) pstate"

text \<open>Definition 5\<close>
definition sem :: "('pvar, 'pval) stmt \<Rightarrow> ('lvar, 'lval, 'pvar, 'pval) state set \<Rightarrow> ('lvar, 'lval, 'pvar, 'pval) state set" where
  "sem C S = { (l, \<sigma>') |\<sigma>' \<sigma> l. (l, \<sigma>) \<in> S \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>' }"

lemma in_sem:
  "\<phi> \<in> sem C S \<longleftrightarrow> (\<exists>\<sigma>. (fst \<phi>, \<sigma>) \<in> S \<and> single_sem C \<sigma> (snd \<phi>))" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain \<sigma>' \<sigma> l where "\<phi> = (l, \<sigma>')" "(l, \<sigma>) \<in> S \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
    using sem_def[of C S] by auto
  then show ?B
    by auto
next
  show "?B \<Longrightarrow> ?A"
    by (metis (mono_tags, lifting) CollectI prod.collapse sem_def)
qed

text \<open>Useful properties\<close>

lemma sem_seq:
  "sem (Seq C1 C2) S = sem C2 (sem C1 S)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix x2 assume "x2 \<in> ?A"
    then obtain x0 where "(fst x2, x0) \<in> S" "single_sem (Seq C1 C2) x0 (snd x2)"
      by (metis in_sem)
    then obtain x1 where "single_sem C1 x0 x1" "single_sem C2 x1 (snd x2)"
      using single_sem_Seq_elim[of C1 C2 x0 "snd x2"]
      by blast
    then show "x2 \<in> ?B"
      by (metis \<open>(fst x2, x0) \<in> S\<close> fst_conv in_sem snd_conv)
  qed
  show "?B \<subseteq> ?A"
  proof
    fix x2 assume "x2 \<in> ?B"
    then obtain x1 where "(fst x2, x1) \<in> sem C1 S" "single_sem C2 x1 (snd x2)"
      by (metis in_sem)
    then obtain x0 where "(fst x2, x0) \<in> S" "single_sem C1 x0 x1"
      by (metis fst_conv in_sem snd_conv)
    then have "single_sem (Seq C1 C2) x0 (snd x2)"
      by (simp add: SemSeq \<open>\<langle>C2, x1\<rangle> \<rightarrow> snd x2\<close>)
    then show "x2 \<in> ?A"
      by (meson \<open>(fst x2, x0) \<in> S\<close> in_sem)
  qed
qed

lemma sem_skip:
  "sem Skip S = S"
  using single_sem_Skip_elim SemSkip in_sem[of _ Skip S]
  by fastforce

lemma sem_union:
  "sem C (S1 \<union> S2) = sem C S1 \<union> sem C S2" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" 
  proof
    fix x assume "x \<in> ?A"
    then obtain y where "(fst x, y) \<in> S1 \<union> S2" "single_sem C y (snd x)"
      using in_sem by blast
    then show "x \<in> ?B"
      by (metis Un_iff in_sem)
  qed
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> ?B"
    show "x \<in> ?A"
    proof (cases "x \<in> sem C S1")
      case True
      then show ?thesis
        by (metis IntD2 Un_Int_eq(3) in_sem)
    next
      case False
      then show ?thesis
        by (metis Un_iff \<open>x \<in> sem C S1 \<union> sem C S2\<close> in_sem)
    qed
  qed
qed

lemma sem_union_general:
  "sem C (\<Union>x. f x) = (\<Union>x. sem C (f x))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix b assume "b \<in> ?A"
    then obtain a where "a \<in> (\<Union>x. f x)" "fst a = fst b" "single_sem C (snd a) (snd b)"
      by (metis fst_conv in_sem snd_conv)
    then obtain x where "a \<in> f x" by blast
    then have "b \<in> sem C (f x)"
      by (metis \<open>\<langle>C, snd a\<rangle> \<rightarrow> snd b\<close> \<open>fst a = fst b\<close> in_sem surjective_pairing)
    then show "b \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof
    fix y assume "y \<in> ?B"
    then obtain x where "y \<in> sem C (f x)"
      by blast
    then show "y \<in> ?A"
      by (meson UN_I in_sem iso_tuple_UNIV_I)
  qed
qed

lemma sem_monotonic:
  assumes "S \<subseteq> S'"
  shows "sem C S \<subseteq> sem C S'"
  by (metis assms sem_union subset_Un_eq)

lemma subsetPairI:
  assumes "\<And>l \<sigma>. (l, \<sigma>) \<in> A \<Longrightarrow> (l, \<sigma>) \<in> B"
  shows "A \<subseteq> B"
  by (simp add: assms subrelI)


lemma sem_if:
  "sem (If C1 C2) S = sem C1 S \<union> sem C2 S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix l y assume "(l, y) \<in> ?A"
    then obtain x where "(l, x) \<in> S" "single_sem (If C1 C2) x y"
      by (metis fst_conv in_sem snd_conv)
    then show "(l, y) \<in> ?B" using single_sem_If_elim
      UnI1 UnI2 in_sem
      by (metis fst_conv snd_conv)
  qed
  show "?B \<subseteq> ?A"
    using SemIf1 SemIf2 in_sem
    by (metis (no_types, lifting) Un_subset_iff subsetI)
qed

lemma sem_assume:
  "sem (Assume b) S = { (l, \<sigma>) |l \<sigma>. (l, \<sigma>) \<in> S \<and> b \<sigma> }" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix l y assume "(l, y) \<in> ?A" then obtain x where "(l, x) \<in> S" "single_sem (Assume b) x y"
      using in_sem
      by (metis fst_conv snd_conv)
    then show "(l, y) \<in> ?B" using single_sem_Assume_elim by blast
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetPairI)
    fix l \<sigma> assume asm0: "(l, \<sigma>) \<in> {(l, \<sigma>) |l \<sigma>. (l, \<sigma>) \<in> S \<and> b \<sigma>}"
    then have "(l, \<sigma>) \<in> S" "b \<sigma>" by simp_all
    then show "(l, \<sigma>) \<in> sem (Assume b) S"
      by (metis SemAssume fst_eqD in_sem snd_eqD)
  qed
qed

lemma while_then_reaches:
  assumes "(single_sem C)\<^sup>*\<^sup>* \<sigma> \<sigma>''"
  shows "single_sem (While C) \<sigma> \<sigma>''"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then show ?case
    by (simp add: SemWhileExit)
next
  case (step y z)
  then show ?case
    using SemWhileIter by blast
qed

lemma in_closure_then_while:
  assumes "single_sem C' \<sigma> \<sigma>''"
  shows "\<And>C. C' = While C \<Longrightarrow> (single_sem C)\<^sup>*\<^sup>* \<sigma> \<sigma>''"
  using assms
proof (induct rule: single_sem.induct)
  case (SemWhileIter \<sigma> C' \<sigma>' \<sigma>'')
  then show ?case
    by (metis (no_types, lifting) rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl rtranclp_trans stmt.inject(6))
next
  case (SemWhileExit \<sigma> C')
  then show ?case
    by blast
qed (auto)

theorem loop_equiv:
  "single_sem (While C) \<sigma> \<sigma>' \<longleftrightarrow> (single_sem C)\<^sup>*\<^sup>* \<sigma> \<sigma>'"
  using in_closure_then_while while_then_reaches by blast


fun iterate_sem where
  "iterate_sem 0 _ S = S"
| "iterate_sem (Suc n) C S = sem C (iterate_sem n C S)"

lemma in_iterate_then_in_trans:
  assumes "(l, \<sigma>'') \<in> iterate_sem n C S"
  shows "\<exists>\<sigma>. (l, \<sigma>) \<in> S \<and> (single_sem C)\<^sup>*\<^sup>* \<sigma> \<sigma>''"
  using assms
proof (induct n arbitrary: \<sigma>'' S)
  case 0
  then show ?case
    using iterate_sem.simps(1) by blast
next
  case (Suc n)
  then show ?case
    using in_sem rtranclp.rtrancl_into_rtrancl
    by (metis (mono_tags, lifting) fst_conv iterate_sem.simps(2) snd_conv)
qed

lemma reciprocal:
  assumes "(single_sem C)\<^sup>*\<^sup>* \<sigma> \<sigma>''"
      and "(l, \<sigma>) \<in> S"
    shows "\<exists>n. (l, \<sigma>'') \<in> iterate_sem n C S"
  using assms
proof (induct rule: rtranclp_induct)
  case base
  then show ?case
    using iterate_sem.simps(1) by blast
next
  case (step y z)
  then obtain n where "(l, y) \<in> iterate_sem n C S" by blast
  then show ?case
    using in_sem iterate_sem.simps(2) step.hyps(2)
    by (metis fst_eqD snd_eqD)
qed

lemma union_iterate_sem_trans:
  "(l, \<sigma>'') \<in> (\<Union>n. iterate_sem n C S) \<longleftrightarrow> (\<exists>\<sigma>. (l, \<sigma>) \<in> S \<and> (single_sem C)\<^sup>*\<^sup>* \<sigma> \<sigma>'')" (is "?A \<longleftrightarrow> ?B")
  using in_iterate_then_in_trans reciprocal by auto

lemma sem_while:
  "sem (While C) S = (\<Union>n. iterate_sem n C S)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix l y assume "(l, y) \<in> ?A"
    then obtain x where x_def: "(l, x) \<in> S" "(single_sem C)\<^sup>*\<^sup>* x y"
      using in_closure_then_while in_sem
      by (metis fst_eqD snd_conv)
    then have "single_sem (While C) x y"
      using while_then_reaches by blast
    then show "(l, y) \<in> ?B"
      by (metis x_def union_iterate_sem_trans)
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetPairI)
    fix l y assume "(l, y) \<in> ?B"
    then obtain x where "(l, x) \<in> S" "(single_sem C)\<^sup>*\<^sup>* x y"
      using union_iterate_sem_trans by blast
    then show "(l, y) \<in> ?A"
      using in_sem while_then_reaches by fastforce
  qed
qed


lemma assume_sem:
  "sem (Assume b) S = Set.filter (b \<circ> snd) S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix l \<sigma>
    assume asm0: "(l, \<sigma>) \<in> sem (Assume b) S"
    then show "(l, \<sigma>) \<in> Set.filter (b \<circ> snd) S"
      by (metis comp_apply fst_conv in_sem member_filter single_sem_Assume_elim snd_conv)
  qed
  show "?B \<subseteq> ?A"
    by (metis (mono_tags, opaque_lifting) SemAssume comp_apply in_sem member_filter prod.collapse subsetI)
qed

lemma sem_split_general:
  "sem C (\<Union>x. F x) = (\<Union>x. sem C (F x))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix l \<sigma>'
    assume asm0: "(l, \<sigma>') \<in> sem C (\<Union> (range F))"
    then obtain x \<sigma> where "(l, \<sigma>) \<in> F x" "single_sem C \<sigma> \<sigma>'"
      by (metis (no_types, lifting) UN_iff fst_conv in_sem snd_conv)
    then show "(l, \<sigma>') \<in> (\<Union>x. sem C (F x))"
      using asm0 sem_union_general by blast
  qed
  show "?B \<subseteq> ?A"
    by (simp add: SUP_least Sup_upper sem_monotonic)
qed


end