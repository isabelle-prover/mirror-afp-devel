theory MLSS_Calculus
  imports "HOL-Library.Sublist" MLSS_Semantics MLSS_Typing_Defs
begin

section \<open>A Tableau Calculus for MLSS\<close>
text \<open>
  In this theory, we define a tableau calculus for MLSS.
\<close>

subsection \<open>Closedness\<close>

fun member_seq :: "'a pset_term \<Rightarrow> 'a pset_atom list \<Rightarrow> 'a pset_term \<Rightarrow> bool" where
  "member_seq s [] t \<longleftrightarrow> s = t"
| "member_seq s ((s' \<in>\<^sub>s u) # cs) t \<longleftrightarrow> s = s' \<and> member_seq u cs t"
| "member_seq _ _ _ \<longleftrightarrow> False"

fun member_cycle :: "'a pset_atom list \<Rightarrow> bool" where
  "member_cycle ((s \<in>\<^sub>s t) # cs) = member_seq s ((s \<in>\<^sub>s t) # cs) s"
| "member_cycle _ = False"

inductive bclosed :: "'a branch \<Rightarrow> bool" where
  contr: "\<lbrakk> \<phi> \<in> set b; Neg \<phi> \<in> set b \<rbrakk> \<Longrightarrow> bclosed b"
| memEmpty: "AT (t \<in>\<^sub>s (\<emptyset> n)) \<in> set b \<Longrightarrow> bclosed b"
| neqSelf: "AF (t =\<^sub>s t) \<in> set b \<Longrightarrow> bclosed b"
| memberCycle: "\<lbrakk> member_cycle cs; set cs \<subseteq> Atoms (set b) \<rbrakk> \<Longrightarrow> bclosed b"

abbreviation "bopen b \<equiv> \<not> bclosed b"

subsection \<open>Linear Expansion Rules\<close>

fun tlvl_terms :: "'a pset_atom \<Rightarrow> 'a pset_term set" where
  "tlvl_terms (t1 \<in>\<^sub>s t2) = {t1, t2}"
| "tlvl_terms (t1 =\<^sub>s t2) = {t1, t2}"

lemma tlvl_intros[intro, simp]:
  "t1 \<in> tlvl_terms (t1 \<in>\<^sub>s t2)"
  "t2 \<in> tlvl_terms (t2 \<in>\<^sub>s t1)"
  "t1 \<in> tlvl_terms (t1 =\<^sub>s t2)"
  "t2 \<in> tlvl_terms (t2 =\<^sub>s t1)"
  by auto
  
fun subst_tlvl :: "'a pset_term \<Rightarrow> 'a pset_term \<Rightarrow> 'a pset_atom \<Rightarrow> 'a pset_atom" where
  "subst_tlvl t1 t2 (s1 \<in>\<^sub>s s2) =
    (if s1 = t1 then t2 else s1) \<in>\<^sub>s (if s2 = t1 then t2 else s2)"
| "subst_tlvl t1 t2 (s1 =\<^sub>s s2) =
    (if s1 = t1 then t2 else s1) =\<^sub>s (if s2 = t1 then t2 else s2)"

inductive lexpands_fm :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "And p q \<in> set b \<Longrightarrow> lexpands_fm [p, q] b"
| "Neg (Or p q) \<in> set b \<Longrightarrow> lexpands_fm [Neg p, Neg q] b"
| "\<lbrakk> Or p q \<in> set b; Neg p \<in> set b \<rbrakk> \<Longrightarrow> lexpands_fm [q] b"
| "\<lbrakk> Or p q \<in> set b; Neg q \<in> set b \<rbrakk> \<Longrightarrow> lexpands_fm [p] b"
| "\<lbrakk> Neg (And p q) \<in> set b; p \<in> set b \<rbrakk> \<Longrightarrow> lexpands_fm [Neg q] b"
| "\<lbrakk> Neg (And p q) \<in> set b; q \<in> set b \<rbrakk> \<Longrightarrow> lexpands_fm [Neg p] b"
| "Neg (Neg p) \<in> set b \<Longrightarrow> lexpands_fm [p] b"

inductive lexpands_un :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b \<Longrightarrow> lexpands_un [AF (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms (last b) \<rbrakk>
    \<Longrightarrow> lexpands_un [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms (last b) \<rbrakk>
    \<Longrightarrow> lexpands_un [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b; AF (s \<in>\<^sub>s t1) \<in> set b \<rbrakk>
    \<Longrightarrow> lexpands_un [AT (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b \<rbrakk>
    \<Longrightarrow> lexpands_un [AT (s \<in>\<^sub>s t1)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms (last b) \<rbrakk>
    \<Longrightarrow> lexpands_un [AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b"

inductive lexpands_int :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b \<Longrightarrow> lexpands_int [AT (s \<in>\<^sub>s t1), AT (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b) \<rbrakk>
    \<Longrightarrow> lexpands_int [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t2) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b) \<rbrakk>
    \<Longrightarrow> lexpands_int [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b; AT (s \<in>\<^sub>s t1) \<in> set b \<rbrakk>
    \<Longrightarrow> lexpands_int [AF (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b; AT (s \<in>\<^sub>s t2) \<in> set b \<rbrakk>
    \<Longrightarrow> lexpands_int [AF (s \<in>\<^sub>s t1)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; AT (s \<in>\<^sub>s t2) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b) \<rbrakk>
    \<Longrightarrow> lexpands_int [AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b"

inductive lexpands_diff :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b \<Longrightarrow> lexpands_diff [AT (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1) \<in> set b; t1 -\<^sub>s t2 \<in> subterms (last b) \<rbrakk>
    \<Longrightarrow> lexpands_diff [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t2) \<in> set b; t1 -\<^sub>s t2 \<in> subterms (last b) \<rbrakk>
    \<Longrightarrow> lexpands_diff [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b; AT (s \<in>\<^sub>s t1) \<in> set b \<rbrakk>
    \<Longrightarrow> lexpands_diff [AT (s \<in>\<^sub>s t2)] b"
| "\<lbrakk> AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b \<rbrakk>
    \<Longrightarrow> lexpands_diff [AF (s \<in>\<^sub>s t1)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; AF (s \<in>\<^sub>s t2) \<in> set b; t1 -\<^sub>s t2 \<in> subterms (last b) \<rbrakk>
    \<Longrightarrow> lexpands_diff [AT (s \<in>\<^sub>s t1 -\<^sub>s t2)] b"

inductive lexpands_single :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "Single t1 \<in> subterms (last b) \<Longrightarrow> lexpands_single [AT (t1 \<in>\<^sub>s Single t1)] b"
| "AT (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> lexpands_single [AT (s =\<^sub>s t1)] b"
| "AF (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> lexpands_single [AF (s =\<^sub>s t1)] b"

inductive lexpands_eq :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> AT (t1 =\<^sub>s t2) \<in> set b; AT l \<in> set b; t1 \<in> tlvl_terms l \<rbrakk>
    \<Longrightarrow> lexpands_eq [AT (subst_tlvl t1 t2 l)] b"
| "\<lbrakk> AT (t1 =\<^sub>s t2) \<in> set b; AF l \<in> set b; t1 \<in> tlvl_terms l \<rbrakk>
    \<Longrightarrow> lexpands_eq [AF (subst_tlvl t1 t2 l)] b"
| "\<lbrakk> AT (t1 =\<^sub>s t2) \<in> set b; AT l \<in> set b; t2 \<in> tlvl_terms l \<rbrakk>
    \<Longrightarrow> lexpands_eq [AT (subst_tlvl t2 t1 l)] b"
| "\<lbrakk> AT (t1 =\<^sub>s t2) \<in> set b; AF l \<in> set b; t2 \<in> tlvl_terms l \<rbrakk>
    \<Longrightarrow> lexpands_eq [AF (subst_tlvl t2 t1 l)] b"
| "\<lbrakk> AT (s \<in>\<^sub>s t) \<in> set b; AF (s' \<in>\<^sub>s t) \<in> set b \<rbrakk>
    \<Longrightarrow> lexpands_eq [AF (s =\<^sub>s s')] b"

fun polarise :: "bool \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
  "polarise True \<phi> = \<phi>"
| "polarise False \<phi> = Neg \<phi>"

lemma lexpands_eq_induct'[consumes 1, case_names subst neq]:
  assumes "lexpands_eq b' b"
  assumes "\<And>t1 t2 t1' t2' p l b. 
      \<lbrakk> AT (t1 =\<^sub>s t2) \<in> set b; polarise p (Atom l) \<in> set b;
       (t1', t2') \<in> {(t1, t2), (t2, t1)}; t1' \<in> tlvl_terms l \<rbrakk>
      \<Longrightarrow> P [polarise p (Atom (subst_tlvl t1' t2' l))] b"
  assumes "\<And>s t s' b. \<lbrakk> AT (s \<in>\<^sub>s t) \<in> set b; AF (s' \<in>\<^sub>s t) \<in> set b \<rbrakk> \<Longrightarrow> P [AF (s =\<^sub>s s')] b"
  shows "P b' b"
  using assms(1)
  apply(induction rule: lexpands_eq.induct)
  by (metis assms(2-) insertI1 insertI2 polarise.simps)+

inductive lexpands :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "lexpands_fm b' b \<Longrightarrow> lexpands b' b"
| "lexpands_un b' b \<Longrightarrow> lexpands b' b"
| "lexpands_int b' b \<Longrightarrow> lexpands b' b"
| "lexpands_diff b' b \<Longrightarrow> lexpands b' b"
| "lexpands_single b' b \<Longrightarrow> lexpands b' b"
| "lexpands_eq b' b \<Longrightarrow> lexpands b' b"

lemma lexpands_induct[consumes 1]:
  assumes "lexpands b' b"
  shows "
    (\<And>p q b. And p q \<in> set b \<Longrightarrow> P [p, q] b) \<Longrightarrow>
    (\<And>p q b. Neg (Or p q) \<in> set b \<Longrightarrow> P [Neg p, Neg q] b) \<Longrightarrow>
    (\<And>p q b. Or p q \<in> set b \<Longrightarrow> Neg p \<in> set b \<Longrightarrow> P [q] b) \<Longrightarrow>
    (\<And>p q b. Or p q \<in> set b \<Longrightarrow> Neg q \<in> set b \<Longrightarrow> P [p] b) \<Longrightarrow>
    (\<And>p q b. Neg (And p q) \<in> set b \<Longrightarrow> p \<in> set b \<Longrightarrow> P [Neg q] b) \<Longrightarrow>
    (\<And>p q b. Neg (And p q) \<in> set b \<Longrightarrow> q \<in> set b \<Longrightarrow> P [Neg p] b) \<Longrightarrow>
    (\<And>p b. Neg (Neg p) \<in> set b \<Longrightarrow> P [p] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AF (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms (last b) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t2 b t1. AT (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms (last b) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AF (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 \<squnion>\<^sub>s t2 \<in> subterms (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t1), AT (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AF (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t2 b t1. AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b \<Longrightarrow> AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> P [AF (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2) \<in> set b \<Longrightarrow> AT (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AF (s \<in>\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> AT (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AT (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t1),  AF (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AF (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t2 b t1. AT (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms (last b) \<Longrightarrow> P [AF (s \<in>\<^sub>s t1 -\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b \<Longrightarrow> AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> P [AT (s \<in>\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>s t1 t2 b. AF (s \<in>\<^sub>s t1 -\<^sub>s t2) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> P [AF (s \<in>\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>s t1 b t2. AT (s \<in>\<^sub>s t1) \<in> set b \<Longrightarrow> AF (s \<in>\<^sub>s t2) \<in> set b \<Longrightarrow> t1 -\<^sub>s t2 \<in> subterms (last b) \<Longrightarrow> P [AT (s \<in>\<^sub>s t1 -\<^sub>s t2)] b) \<Longrightarrow>
    (\<And>t1 b. Single t1 \<in> subterms (last b) \<Longrightarrow> P [AT (t1 \<in>\<^sub>s Single t1)] b) \<Longrightarrow>
    (\<And>s t1 b. AT (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> P [AT (s =\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>s t1 b. AF (s \<in>\<^sub>s Single t1) \<in> set b \<Longrightarrow> P [AF (s =\<^sub>s t1)] b) \<Longrightarrow>
    (\<And>t1 t2 b l. AT (t1 =\<^sub>s t2) \<in> set b \<Longrightarrow> AT l \<in> set b \<Longrightarrow> t1 \<in> tlvl_terms l \<Longrightarrow> P [AT (subst_tlvl t1 t2 l)] b) \<Longrightarrow>
    (\<And>t1 t2 b l. AT (t1 =\<^sub>s t2) \<in> set b \<Longrightarrow> AF l \<in> set b \<Longrightarrow> t1 \<in> tlvl_terms l \<Longrightarrow> P [AF (subst_tlvl t1 t2 l)] b) \<Longrightarrow>
    (\<And>t1 t2 b l. AT (t1 =\<^sub>s t2) \<in> set b \<Longrightarrow> AT l \<in> set b \<Longrightarrow> t2 \<in> tlvl_terms l \<Longrightarrow> P [AT (subst_tlvl t2 t1 l)] b) \<Longrightarrow>
    (\<And>t1 t2 b l. AT (t1 =\<^sub>s t2) \<in> set b \<Longrightarrow> AF l \<in> set b \<Longrightarrow> t2 \<in> tlvl_terms l \<Longrightarrow> P [AF (subst_tlvl t2 t1 l)] b) \<Longrightarrow>  
    (\<And>s t b s'. AT (s \<in>\<^sub>s t) \<in> set b \<Longrightarrow> AF (s' \<in>\<^sub>s t) \<in> set b \<Longrightarrow> P [AF (s =\<^sub>s s')] b) \<Longrightarrow> P b' b"
  using assms
  apply(induction rule: lexpands.induct)
  subgoal apply(induction rule: lexpands_fm.induct) by metis+
  subgoal apply(induction rule: lexpands_un.induct) by metis+
  subgoal apply(induction rule: lexpands_int.induct) by metis+
  subgoal apply(induction rule: lexpands_diff.induct) by metis+
  subgoal apply(induction rule: lexpands_single.induct) by metis+
  subgoal apply(induction rule: lexpands_eq.induct) by metis+
  done


subsection \<open>Fulfilling Expansion Rules\<close>

inductive bexpands_nowit :: "'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "\<lbrakk> Or p q \<in> set b;
     p \<notin> set b; Neg p \<notin> set b \<rbrakk>
    \<Longrightarrow> bexpands_nowit {[p], [Neg p]} b"
| "\<lbrakk> Neg (And p q) \<in> set b;
     Neg p \<notin> set b; p \<notin> set b \<rbrakk>
    \<Longrightarrow> bexpands_nowit {[Neg p], [p]} b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t2) \<in> set b; t1 \<squnion>\<^sub>s t2 \<in> subterms (last b);
     AT (s \<in>\<^sub>s t1) \<notin> set b; AF (s \<in>\<^sub>s t1) \<notin> set b \<rbrakk>
    \<Longrightarrow> bexpands_nowit {[AT (s \<in>\<^sub>s t1)], [AF (s \<in>\<^sub>s t1)]} b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; t1 \<sqinter>\<^sub>s t2 \<in> subterms (last b);
     AT (s \<in>\<^sub>s t2) \<notin> set b; AF (s \<in>\<^sub>s t2) \<notin> set b \<rbrakk>
    \<Longrightarrow> bexpands_nowit {[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]} b"
| "\<lbrakk> AT (s \<in>\<^sub>s t1) \<in> set b; t1 -\<^sub>s t2 \<in> subterms (last b);
     AT (s \<in>\<^sub>s t2) \<notin> set b; AF (s \<in>\<^sub>s t2) \<notin> set b \<rbrakk>
    \<Longrightarrow> bexpands_nowit {[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]} b"

inductive bexpands_wit ::
  "'a pset_term \<Rightarrow> 'a pset_term \<Rightarrow> 'a \<Rightarrow> 'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" for t1 t2 x where
  "\<lbrakk> AF (t1 =\<^sub>s t2) \<in> set b; t1 \<in> subterms (last b); t2 \<in> subterms (last b);
     \<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b;
     \<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set b \<and> AF (x \<in>\<^sub>s t1) \<in> set b;
     x \<notin> vars b; \<not> urelem (last b) t1; \<not> urelem (last b) t2 \<rbrakk>
    \<Longrightarrow> bexpands_wit t1 t2 x {[AT (Var x \<in>\<^sub>s t1), AF (Var x \<in>\<^sub>s t2)],
                              [AT (Var x \<in>\<^sub>s t2), AF (Var x \<in>\<^sub>s t1)]} b"

inductive_cases bexpands_wit_cases[consumes 1]: "bexpands_wit t1 t2 x bs' b"

lemma bexpands_witD:
  assumes "bexpands_wit t1 t2 x bs' b"
  shows "bs' = {[AT (Var x \<in>\<^sub>s t1), AF (Var x \<in>\<^sub>s t2)],
               [AT (Var x \<in>\<^sub>s t2), AF (Var x \<in>\<^sub>s t1)]}"
        "AF (t1 =\<^sub>s t2) \<in> set b" "t1 \<in> subterms (last b)" "t2 \<in> subterms (last b)"
        "\<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b"
        "\<nexists>x. AT (x \<in>\<^sub>s t2) \<in> set b \<and> AF (x \<in>\<^sub>s t1) \<in> set b"
        "\<not> urelem (last b) t1" "\<not> urelem (last b) t2"
        "x \<notin> vars b"
  using bexpands_wit.cases[OF assms] by metis+

inductive bexpands :: "'a branch set \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "bexpands_nowit bs' b \<Longrightarrow> bexpands bs' b"
| "bexpands_wit t1 t2 x bs' b \<Longrightarrow> bexpands bs' b"

lemma bexpands_disjnt:
  assumes "bexpands bs' b" "b' \<in> bs'"
  shows "set b \<inter> set b' = {}"
  using assms
proof(induction bs' b rule: bexpands.induct)
  case (1 bs b)
  then show ?case
    by (induction rule: bexpands_nowit.induct) (auto intro: list.set_intros(1))
next
  case (2 t1 t2 x bs b)
  then show ?case
  proof(induction rule: bexpands_wit.induct)
    case (1 b)
    from \<open>x \<notin> vars b\<close>
    have "AT (Var x \<in>\<^sub>s t1) \<notin> set b" "AF (Var x \<in>\<^sub>s t1) \<notin> set b"
      unfolding vars_branch_def by auto
    with 1 show ?case
      by (auto intro: list.set_intros(1) simp: disjnt_iff vars_fm_vars_branchI)
  qed
qed

lemma bexpands_branch_not_Nil:
  assumes "bexpands bs' b" "b' \<in> bs'"
  shows "b' \<noteq> []"
  using assms
proof(induction bs' b rule: bexpands.induct)
  case (1 bs' b)
  then show ?case
    by (induction rule: bexpands_nowit.induct) auto
next
  case (2 t1 t2 x bs' b)
  then show ?case
    by (induction rule: bexpands_wit.induct) auto
qed

lemma bexpands_nonempty: "bexpands bs' b \<Longrightarrow> bs' \<noteq> {}"
proof(induction rule: bexpands.induct)
  case (1 bs' b)
  then show ?case by (induction rule: bexpands_nowit.induct) auto
next
  case (2 t1 t2 x bs' b)
  then show ?case by (induction rule: bexpands_wit.induct) auto
qed

lemma bexpands_strict_mono:
  assumes "bexpands bs' b" "b' \<in> bs'"
  shows "set b \<subset> set (b' @ b)"
  using bexpands_disjnt[OF assms] bexpands_branch_not_Nil[OF assms]
  by (simp add: less_le) (metis Un_Int_eq(1) set_empty2)

inductive_cases bexpands_cases[consumes 1, case_names no_param param]: "bexpands bs b"


subsection \<open>Expansion Closure\<close>

inductive expandss :: "'a branch \<Rightarrow> 'a branch \<Rightarrow> bool" where
  "expandss b b"
| "lexpands b3 b2 \<Longrightarrow> set b2 \<subset> set (b3 @ b2) \<Longrightarrow> expandss b2 b1 \<Longrightarrow> expandss (b3 @ b2) b1"
| "bexpands bs b2 \<Longrightarrow> b3 \<in> bs \<Longrightarrow> expandss b2 b1 \<Longrightarrow> expandss (b3 @ b2) b1"

lemma expandss_trans: "expandss b3 b2 \<Longrightarrow> expandss b2 b1 \<Longrightarrow> expandss b3 b1"
  by (induction rule: expandss.induct) (auto simp: expandss.intros)

lemma expandss_suffix:
  "expandss b1 b2 \<Longrightarrow> suffix b2 b1"
  apply(induction rule: expandss.induct)
    apply(auto simp: suffix_appendI)
  done

lemmas expandss_mono = set_mono_suffix[OF expandss_suffix]

lemma expandss_last_eq[simp]:
  "expandss b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> last b' = last b"
  by (metis expandss_suffix last_appendR suffix_def)

lemma expandss_not_Nil:
  "expandss b' b \<Longrightarrow> b \<noteq> [] \<Longrightarrow> b' \<noteq> []"
  using expandss_suffix suffix_bot.extremum_uniqueI by blast


subsection \<open>Well-Formed Branch\<close>

definition "wf_branch b \<equiv> \<exists>\<phi>. expandss b [\<phi>]"

lemma wf_branch_singleton[simp]: "wf_branch [\<phi>]"
  unfolding wf_branch_def using expandss.intros(1) by blast

lemma wf_branch_not_Nil[simp, intro?]: "wf_branch b \<Longrightarrow> b \<noteq> []"
  unfolding wf_branch_def
  using expandss_suffix suffix_bot.extremum_uniqueI by blast

lemma wf_branch_expandss: "wf_branch b \<Longrightarrow> expandss b' b \<Longrightarrow> wf_branch b'"
  using expandss_trans wf_branch_def by blast

lemma wf_branch_lexpands:
  "wf_branch b \<Longrightarrow> lexpands b' b \<Longrightarrow> set b \<subset> set (b' @ b) \<Longrightarrow> wf_branch (b' @ b)"
  by (metis expandss.simps wf_branch_expandss)

end