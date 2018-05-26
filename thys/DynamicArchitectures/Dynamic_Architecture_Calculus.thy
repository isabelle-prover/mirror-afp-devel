(*
  Title:      Dynamic_Architecture_Calculus
  Author:     Diego Marmsoler
*)
section "A Calculus for Dynamic Architectures"
text {*
  The following theory formalizes our calculus for dynamic architectures~\cite{Marmsoler2017b,Marmsoler2017c} and verifies its soundness.
  The calculus allows to reason about temporal-logic specifications of component behavior in a dynamic setting.
  The theory is based on our theory of configuration traces and introduces the notion of behavior trace assertion to specify component behavior in a dynamic setting.
*}
theory Dynamic_Architecture_Calculus
  imports Configuration_Traces
begin

subsection "Extended Natural Numbers"
text {*
  We first provide one additional property for extended natural numbers.
*}

lemma the_enat_mono[simp]:
  assumes "m \<noteq> \<infinity>"
    and "n \<le> m"
  shows "the_enat n \<le> the_enat m"
  using assms(1) assms(2) enat_ile by fastforce
    
subsection "Lazy Lists"
text {*
  Finally, we provide an additional property for lazy lists.
*}
  
lemma llength_geq_enat_lfiniteD: "llength xs \<le> enat n \<Longrightarrow> lfinite xs"
  using not_lfinite_llength by force

context dynamic_component
begin

subsection "Dynamic Evaluation of Temporal Operators"
text {*
  In the following we introduce a function to evaluate a behavior trace assertion over a given configuration trace.
*}

definition eval:: "'id \<Rightarrow> (nat \<Rightarrow> cnf) \<Rightarrow> (nat \<Rightarrow> 'cmp) \<Rightarrow> nat
  \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool"
  where "eval cid t t' n \<gamma> \<equiv>
    (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>) \<and> \<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat(\<langle>cid #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<or>
    (\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>) \<and> (\<nexists>i'. i'\<ge>n \<and> \<parallel>cid\<parallel>\<^bsub>t i'\<^esub>) \<and> \<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>(n)) \<or>
    (\<nexists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>) \<and> \<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) n"
text {*
  @{const eval} takes a component identifier @{term cid}, a configuration trace @{term t}, a behavior trace @{term t'}, and point in time @{term n} and evaluates behavior trace assertion @{term \<gamma>} as follows:
  \begin{itemize}
    \item If component @{term cid} is again activated in the future, @{term \<gamma>} is evaluated at the next point in time where @{term cid} is active in @{term t}.
    \item If component @{term cid} is not again activated in the future but it is activated at least once in @{term t}, then @{term \<gamma>} is evaluated at the point in time given by @{term "(\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>(n))"}.
    \item If component @{term cid} is never active in @{term t}, then @{term \<gamma>} is evaluated at time point @{term n}.
  \end{itemize}
*}
  
text {*
  The following proposition evaluates definition @{const eval} by showing that a behavior trace assertion @{term \<gamma>} holds over configuration trace @{term t} and continuation @{term t'} whenever it holds for the concatenation of the corresponding projection with @{term t'}.
*}
proposition eval_corr:
  "eval cid t t' 0 \<gamma> \<longleftrightarrow> \<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) 0"
proof
  assume "eval cid t t' 0 \<gamma>"
  with eval_def have "(\<exists>i\<ge>0. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>) \<and>
  \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat 0\<^esub>inf_llist t\<rangle>) \<or>
  (\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>) \<and> \<not> (\<exists>i'\<ge>0. \<parallel>cid\<parallel>\<^bsub>t i'\<^esub>) \<and> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>0) \<or>
  (\<nexists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>) \<and> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) 0" by simp
  thus "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) 0"
  proof
    assume "(\<exists>i\<ge>0. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>) \<and> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat 0\<^esub>inf_llist t\<rangle>)"
    moreover have "the_enat \<langle>cid #\<^bsub>enat 0\<^esub>inf_llist t\<rangle> = 0" using zero_enat_def by auto
    ultimately show ?thesis by simp
  next
    assume "(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>) \<and> \<not> (\<exists>i'\<ge>0. \<parallel>cid\<parallel>\<^bsub>t i'\<^esub>) \<and> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>0) \<or>
    (\<nexists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>) \<and> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) 0"
    thus ?thesis by auto
  qed
next
  assume "\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) 0"
  show "eval cid t t' 0 \<gamma>"
  proof cases
    assume "\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    hence "\<exists>i\<ge>0. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>" by simp
    moreover from `\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) 0` have
      "\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat(\<langle>cid #\<^bsub>enat 0\<^esub> inf_llist t\<rangle>))"
      using zero_enat_def by auto
    ultimately show ?thesis using eval_def by simp
  next
    assume "\<nexists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    with `\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) 0` show ?thesis using eval_def by simp
  qed
qed

subsubsection "Simplification Rules"

lemma validCI_act[simp]:
  assumes "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    and "\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat(\<langle>cid #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
  shows "eval cid t t' n \<gamma>"
  using assms eval_def by simp

lemma validCI_cont[simp]:
  assumes "\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    and "\<nexists>i'. i'\<ge>n \<and> \<parallel>cid\<parallel>\<^bsub>t i'\<^esub>"
    and "\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>(n))"
  shows "eval cid t t' n \<gamma>"
  using assms eval_def by simp

lemma validCI_not_act[simp]:
  assumes "\<nexists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    and "\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) n"
  shows "eval cid t t' n \<gamma>"
  using assms eval_def by simp

lemma validCE_act[simp]:
  assumes "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    and "eval cid t t' n \<gamma>"
  shows "\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat(\<langle>cid #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
  using assms eval_def by auto
    
lemma validCE_cont[simp]:
  assumes "\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    and "\<nexists>i'. i'\<ge>n \<and> \<parallel>cid\<parallel>\<^bsub>t i'\<^esub>"
    and "eval cid t t' n \<gamma>"
  shows "\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>(n))"
  using assms eval_def by auto

lemma validCE_not_act[simp]:
  assumes "\<nexists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    and "eval cid t t' n \<gamma>"
  shows "\<gamma> (lnth ((\<pi>\<^bsub>cid\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) n"
  using assms eval_def by auto
    
subsubsection "No Activations"

proposition validity1:
  assumes "n\<le>n'"
    and "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>k\<ge>n. k<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
  shows "eval c t t' n \<gamma> \<Longrightarrow> eval c t t' n' \<gamma>"
proof -
  assume "eval c t t' n \<gamma>"
  moreover from assms have "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by (meson order.trans)
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>))"
    using validCE_act by blast
  moreover have "enat n' - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
  with assms have "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>) = the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)"
    using nAct_not_active_same[of n n' "inf_llist t" c] by simp
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>))"
    by simp     
  with assms show ?thesis using validCI_act by blast
qed
  
proposition validity2:
  assumes "n\<le>n'"
    and "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>k\<ge>n. k<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
  shows "eval c t t' n' \<gamma> \<Longrightarrow> eval c t t' n \<gamma>"
proof -
  assume "eval c t t' n' \<gamma>"
  with `\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
    have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>))"
    using validCE_act by blast
  moreover have "enat n' - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
  with assms have "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>) = the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)"
    using nAct_not_active_same by simp
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>))"
    by simp     
  moreover from assms have "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by (meson order.trans)      
  ultimately show ?thesis using validCI_act by blast
qed
  
subsection "Basic Operators"
text {*
  In the following we introduce some basic operators for behavior trace assertions.
*}

subsubsection "Predicates"
text {*
  Every predicate can be transformed to a behavior trace assertion.
*}

definition pred :: "bool \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)"
  where "pred P \<equiv> \<lambda> t n. P"

lemma predI[intro]:
  fixes cid t t' n P
  assumes "P"
  shows "eval cid t t' n (pred P)"
proof cases
  assume "(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    with assms show ?thesis using eval_def pred_def by auto
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    with assms show ?thesis using eval_def pred_def by auto
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  with assms show ?thesis using eval_def pred_def by auto
qed    
    
lemma predE[elim]:
  fixes cid t t' n P
  assumes "eval cid t t' n (pred P)"
  shows "P"
proof cases
  assume "(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    with assms show ?thesis using eval_def pred_def by auto
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    with assms show ?thesis using eval_def pred_def by auto
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  with assms show ?thesis using eval_def pred_def by auto
qed

subsubsection "True and False"

definition true :: "(nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool"
  where "true \<equiv> \<lambda>t n. HOL.True"
    
definition false :: "(nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool"
  where "false \<equiv> \<lambda>t n. HOL.False"

subsubsection "Implication"  
  
definition imp :: "((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)
  \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" (infixl "\<longrightarrow>\<^sup>b" 10)
  where "\<gamma> \<longrightarrow>\<^sup>b \<gamma>' \<equiv> \<lambda> t n. \<gamma> t n \<longrightarrow> \<gamma>' t n"

lemma impI[intro!]:
  assumes "eval cid t t' n \<gamma> \<longrightarrow> eval cid t t' n \<gamma>'"
  shows "eval cid t t' n (\<gamma> \<longrightarrow>\<^sup>b \<gamma>')"
proof cases
  assume "\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    with `eval cid t t' n \<gamma> \<longrightarrow> eval cid t t' n \<gamma>'`
      have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)
      \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using eval_def by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<longrightarrow> \<gamma>' t n)"
      using validCI_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<longrightarrow> \<gamma>' t n"] by blast
    thus ?thesis using imp_def by simp
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `eval cid t t' n \<gamma> \<longrightarrow> eval cid t t' n \<gamma>'`
      have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)
      \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)" using eval_def by blast
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<longrightarrow> \<gamma>' t n)"
      using validCI_cont[where \<gamma>="\<lambda> t n. \<gamma> t n \<longrightarrow> \<gamma>' t n"] by blast
    thus ?thesis using imp_def by simp
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  with `eval cid t t' n \<gamma> \<longrightarrow> eval cid t t' n \<gamma>'`
    have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using eval_def by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<longrightarrow> \<gamma>' t n)"
    using validCI_not_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<longrightarrow> \<gamma>' t n"] by blast
  thus ?thesis using imp_def by simp    
qed
    
lemma impE[elim!]:
  assumes "eval cid t t' n (\<gamma> \<longrightarrow>\<^sup>b \<gamma>')"
  shows "eval cid t t' n \<gamma> \<longrightarrow> eval cid t t' n \<gamma>'"
proof cases
  assume "(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    moreover from `eval cid t t' n (\<gamma> \<longrightarrow>\<^sup>b \<gamma>')` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<longrightarrow> \<gamma>' t n)"
      using imp_def by simp
    ultimately have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)
      \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using validCE_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<longrightarrow> \<gamma>' t n"] by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    moreover from `eval cid t t' n (\<gamma> \<longrightarrow>\<^sup>b \<gamma>')` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<longrightarrow> \<gamma>' t n)"
      using imp_def by simp
    ultimately have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)
      \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)"
      using validCE_cont[where \<gamma>="\<lambda> t n. \<gamma> t n \<longrightarrow> \<gamma>' t n"] `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` by blast
    with `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval cid t t' n (\<gamma> \<longrightarrow>\<^sup>b \<gamma>')` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<longrightarrow> \<gamma>' t n)"
    using imp_def by simp
  ultimately have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n
    \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using validCE_not_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<longrightarrow> \<gamma>' t n"] by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using eval_def by blast
qed

subsubsection "Disjunction"  
    
definition or :: "((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)
  \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" (infixl "\<or>\<^sup>b" 15)
  where "\<gamma> \<or>\<^sup>b \<gamma>' \<equiv> \<lambda> t n. \<gamma> t n \<or> \<gamma>' t n"

lemma orI[intro!]:
  assumes "eval cid t t' n \<gamma> \<or> eval cid t t' n \<gamma>'"
  shows "eval cid t t' n (\<gamma> \<or>\<^sup>b \<gamma>')"
proof cases
  assume "\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    with `eval cid t t' n \<gamma> \<or> eval cid t t' n \<gamma>'`
      have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)
      \<or> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using eval_def by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<or> \<gamma>' t n)"
      using validCI_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<or> \<gamma>' t n"] by blast
    thus ?thesis using or_def by simp
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `eval cid t t' n \<gamma> \<or> eval cid t t' n \<gamma>'`
      have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)
      \<or> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)" using eval_def by blast
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<or> \<gamma>' t n)"
      using validCI_cont[where \<gamma>="\<lambda> t n. \<gamma> t n \<or> \<gamma>' t n"] by blast
    thus ?thesis using or_def by simp
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  with `eval cid t t' n \<gamma> \<or> eval cid t t' n \<gamma>'`
    have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n \<or> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using eval_def by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<or> \<gamma>' t n)"
    using validCI_not_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<or> \<gamma>' t n"] by blast
  thus ?thesis using or_def by simp    
qed
    
lemma orE[elim!]:
  assumes "eval cid t t' n (\<gamma> \<or>\<^sup>b \<gamma>')"
  shows "eval cid t t' n \<gamma> \<or> eval cid t t' n \<gamma>'"
proof cases
  assume "(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    moreover from `eval cid t t' n (\<gamma> \<or>\<^sup>b \<gamma>')` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<or> \<gamma>' t n)"
      using or_def by simp
    ultimately have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)
      \<or> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using validCE_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<or> \<gamma>' t n"] by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis
      using validCI_act[of n cid t \<gamma> t'] validCI_act[of n cid t \<gamma>' t'] by blast
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    moreover from `eval cid t t' n (\<gamma> \<or>\<^sup>b \<gamma>')` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<or> \<gamma>' t n)"
      using or_def by simp
    ultimately have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)
      \<or> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)"
      using validCE_cont[where \<gamma>="\<lambda> t n. \<gamma> t n \<or> \<gamma>' t n"] `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` by blast
    with `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis
      using validCI_cont[of cid t n \<gamma> t'] validCI_cont[of cid t n \<gamma>' t'] by blast
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval cid t t' n (\<gamma> \<or>\<^sup>b \<gamma>')` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<or> \<gamma>' t n)"
    using or_def by simp
  ultimately have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n
    \<or> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using validCE_not_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<or> \<gamma>' t n"] by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` show ?thesis
    using validCI_not_act[of cid t \<gamma> t' n] validCI_not_act[of cid t \<gamma>' t' n] by blast
qed

subsubsection "Conjunction"
  
definition "and" :: "((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)
  \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" (infixl "\<and>\<^sup>b" 20)
  where "\<gamma> \<and>\<^sup>b \<gamma>' \<equiv> \<lambda> t n. \<gamma> t n \<and> \<gamma>' t n"

lemma andI[intro!]:
  assumes "eval cid t t' n \<gamma> \<and> eval cid t t' n \<gamma>'"
  shows "eval cid t t' n (\<gamma> \<and>\<^sup>b \<gamma>')"
proof cases
  assume "\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    with `eval cid t t' n \<gamma> \<and> eval cid t t' n \<gamma>'`
      have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)
      \<and> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using eval_def by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<and> \<gamma>' t n)"
      using validCI_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<and> \<gamma>' t n"] by blast
    thus ?thesis using and_def by simp
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `eval cid t t' n \<gamma> \<and> eval cid t t' n \<gamma>'`
      have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)
      \<and> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)" using eval_def by blast
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<and> \<gamma>' t n)"
      using validCI_cont[where \<gamma>="\<lambda> t n. \<gamma> t n \<and> \<gamma>' t n"] by blast
    thus ?thesis using and_def by simp
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  with `eval cid t t' n \<gamma> \<and> eval cid t t' n \<gamma>'` have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n
    \<and> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n" using eval_def by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<and> \<gamma>' t n)"
    using validCI_not_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<and> \<gamma>' t n"] by blast
  thus ?thesis using and_def by simp    
qed
    
lemma andE[elim!]:
  assumes "eval cid t t' n (\<gamma> \<and>\<^sup>b \<gamma>')"
  shows "eval cid t t' n \<gamma> \<and> eval cid t t' n \<gamma>'"
proof cases
  assume "(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    moreover from `eval cid t t' n (\<gamma> \<and>\<^sup>b \<gamma>')` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<and> \<gamma>' t n)"
      using and_def by simp
    ultimately have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)
      \<and> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using validCE_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<and> \<gamma>' t n"] by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    moreover from `eval cid t t' n (\<gamma> \<and>\<^sup>b \<gamma>')` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<and> \<gamma>' t n)"
      using and_def by simp
    ultimately have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)
      \<and> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)"
      using validCE_cont[where \<gamma>="\<lambda> t n. \<gamma> t n \<and> \<gamma>' t n"] `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` by blast
    with `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval cid t t' n (\<gamma> \<and>\<^sup>b \<gamma>')` have "eval cid t t' n (\<lambda>t n. \<gamma> t n \<and> \<gamma>' t n)"
    using and_def by simp
  ultimately have "\<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n \<and> \<gamma>' (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using validCE_not_act[where \<gamma>="\<lambda> t n. \<gamma> t n \<and> \<gamma>' t n"] by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using eval_def by blast
qed

subsubsection "Negation"
  
definition not :: "((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" ("\<not>\<^sup>b _" [19] 19)
  where "\<not>\<^sup>b \<gamma> \<equiv> \<lambda> t n. \<not> \<gamma> t n"
    
lemma notI[intro!]:
  assumes "\<not> eval cid t t' n \<gamma>"
  shows "eval cid t t' n (\<not>\<^sup>b \<gamma>)"
proof cases
  assume "\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    with `\<not> eval cid t t' n \<gamma>`
      have "\<not> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using eval_def by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` have "eval cid t t' n (\<lambda>t n. \<not> \<gamma> t n)"
      using validCI_act[where \<gamma>="\<lambda> t n. \<not> \<gamma> t n"] by blast
    thus ?thesis using not_def by simp
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `\<not> eval cid t t' n \<gamma>`
      have "\<not> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)" using eval_def by blast
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. \<not> \<gamma> t n)"
      using validCI_cont[where \<gamma>="\<lambda> t n. \<not> \<gamma> t n"] by blast
    thus ?thesis using not_def by simp
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  with `\<not> eval cid t t' n \<gamma>` have "\<not> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n" using eval_def by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. \<not> \<gamma> t n)"
    using validCI_not_act[where \<gamma>="\<lambda> t n. \<not> \<gamma> t n"] by blast
  thus ?thesis using not_def by simp    
qed   

lemma notE[elim!]:
  assumes "eval cid t t' n (\<not>\<^sup>b \<gamma>)"
  shows "\<not> eval cid t t' n \<gamma>"
proof cases
  assume "(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    moreover from `eval cid t t' n (\<not>\<^sup>b \<gamma>)` have "eval cid t t' n (\<lambda>t n. \<not> \<gamma> t n)" using not_def by simp
    ultimately have "\<not> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using validCE_act[where \<gamma>="\<lambda> t n. \<not> \<gamma> t n"] by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    moreover from `eval cid t t' n (\<not>\<^sup>b \<gamma>)` have "eval cid t t' n (\<lambda>t n. \<not> \<gamma> t n)" using not_def by simp
    ultimately have "\<not> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)"
      using validCE_cont[where \<gamma>="\<lambda> t n. \<not> \<gamma> t n"] `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` by blast
    with `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval cid t t' n (\<not>\<^sup>b \<gamma>)` have "eval cid t t' n (\<lambda>t n. \<not> \<gamma> t n)" using not_def by simp
  ultimately have "\<not> \<gamma> (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using validCE_not_act[where \<gamma>="\<lambda> t n. \<not> \<gamma> t n"] by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using eval_def by blast
qed

subsubsection "Quantifiers"

definition all :: "('a \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool))
  \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" (binder "\<forall>\<^sub>b" 10)
  where "all P \<equiv> \<lambda>t n. (\<forall>y. (P y t n))"

lemma allI[intro!]:
  assumes "\<forall>p. eval cid t t' n (\<gamma> p)"
  shows "eval cid t t' n (all (\<lambda>p. \<gamma> p))"
proof cases
  assume "\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    with `\<forall>p. eval cid t t' n (\<gamma> p)`
    have "\<forall>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using eval_def by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` have "eval cid t t' n (\<lambda>t n. (\<forall>y. (\<gamma> y t n)))"
      using validCI_act[where \<gamma>="\<lambda>t n. (\<forall>y. (\<gamma> y t n))"] by blast
    thus ?thesis using all_def[of \<gamma>] by auto
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `\<forall>p. eval cid t t' n (\<gamma> p)`
      have "\<forall>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)"
      using eval_def by blast
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. (\<forall>y. (\<gamma> y t n)))"
      using validCI_cont[where \<gamma>="\<lambda>t n. (\<forall>y. (\<gamma> y t n))"] by blast
    thus ?thesis using all_def[of \<gamma>] by auto
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  with `\<forall>p. eval cid t t' n (\<gamma> p)` have "\<forall>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using eval_def by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. (\<forall>y. (\<gamma> y t n)))"
    using validCI_not_act[where \<gamma>="\<lambda>t n. (\<forall>y. (\<gamma> y t n))"] by blast
  thus ?thesis using all_def[of \<gamma>] by auto
qed
  
lemma allE[elim!]:
  assumes "eval cid t t' n (all (\<lambda>p. \<gamma> p))"
  shows "\<forall>p. eval cid t t' n (\<gamma> p)"
proof cases
  assume "(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    moreover from `eval cid t t' n (all (\<lambda>p. \<gamma> p))` have "eval cid t t' n (\<lambda>t n. (\<forall>y. (\<gamma> y t n)))"
      using all_def[of \<gamma>] by auto
    ultimately have "\<forall>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using validCE_act[where \<gamma>="\<lambda>t n. (\<forall>y. (\<gamma> y t n))"] by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    moreover from `eval cid t t' n (all (\<lambda>p. \<gamma> p))` have "eval cid t t' n (\<lambda>t n. (\<forall>y. (\<gamma> y t n)))"
      using all_def[of \<gamma>] by auto
    ultimately have "\<forall>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)"
      using validCE_cont[where \<gamma>="\<lambda>t n. (\<forall>y. (\<gamma> y t n))"] `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` by blast
    with `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval cid t t' n (all (\<lambda>p. \<gamma> p))` have "eval cid t t' n (\<lambda>t n. (\<forall>y. (\<gamma> y t n)))"
    using all_def[of \<gamma>] by auto
  ultimately have "\<forall>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using validCE_not_act[where \<gamma>="\<lambda>t n. (\<forall>y. (\<gamma> y t n))"] by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using eval_def by blast
qed
  
definition exists :: "('a \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool))
  \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" (binder "\<exists>\<^sub>b" 10)
  where "exists P \<equiv> \<lambda>t n. (\<exists>y. (P y t n))"
    
lemma existsI[intro!]:
  assumes "\<exists>p. eval cid t t' n (\<gamma> p)"
  shows "eval cid t t' n (exists (\<lambda>p. \<gamma> p))"
proof cases
  assume "\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    with `\<exists>p. eval cid t t' n (\<gamma> p)`
      have "\<exists>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using eval_def by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` have "eval cid t t' n (\<lambda>t n. (\<exists>y. (\<gamma> y t n)))"
      using validCI_act[where \<gamma>="\<lambda>t n. (\<exists>y. (\<gamma> y t n))"] by blast
    thus ?thesis using exists_def[of \<gamma>] by auto
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `\<exists>p. eval cid t t' n (\<gamma> p)`
      have "\<exists>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)" using eval_def by blast
    with `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. (\<exists>y. (\<gamma> y t n)))"
      using validCI_cont[where \<gamma>="\<lambda>t n. (\<exists>y. (\<gamma> y t n))"] by blast
    thus ?thesis using exists_def[of \<gamma>] by auto
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  with `\<exists>p. eval cid t t' n (\<gamma> p)` have "\<exists>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using eval_def by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` have "eval cid t t' n (\<lambda>t n. (\<exists>y. (\<gamma> y t n)))"
    using validCI_not_act[where \<gamma>="\<lambda>t n. (\<exists>y. (\<gamma> y t n))"] by blast
  thus ?thesis using exists_def[of \<gamma>] by auto
qed
  
lemma existsE[elim!]:
  assumes "eval cid t t' n (exists (\<lambda>p. \<gamma> p))"
  shows "\<exists>p. eval cid t t' n (\<gamma> p)"
proof cases
  assume "(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>"
    moreover from `eval cid t t' n (exists (\<lambda>p. \<gamma> p))` have "eval cid t t' n (\<lambda>t n. (\<exists>y. (\<gamma> y t n)))"
      using exists_def[of \<gamma>] by auto
    ultimately have "\<exists>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (the_enat \<langle>cid #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)"
      using validCE_act[where \<gamma>="\<lambda>t n. (\<exists>y. (\<gamma> y t n))"] by blast
    with `\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  next
    assume "\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
    moreover from `eval cid t t' n (exists (\<lambda>p. \<gamma> p))` have "eval cid t t' n (\<lambda>t n. (\<exists>y. (\<gamma> y t n)))"
      using exists_def[of \<gamma>] by auto
    ultimately have "\<exists>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>cid\<^esub>\<down>\<^bsub>t\<^esub>n)"
      using validCE_cont[where \<gamma>="\<lambda>t n. (\<exists>y. (\<gamma> y t n))"] `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` by blast
    with `\<not> (\<exists>i\<ge>n. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` `\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>` show ?thesis using eval_def by blast
  qed
next
  assume "\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval cid t t' n (exists (\<lambda>p. \<gamma> p))` have "eval cid t t' n (\<lambda>t n. (\<exists>y. (\<gamma> y t n)))"
    using exists_def[of \<gamma>] by auto
  ultimately have "\<exists>p. (\<gamma> p) (lnth (\<pi>\<^bsub>cid\<^esub>inf_llist t @\<^sub>l inf_llist t')) n"
    using validCE_not_act[where \<gamma>="\<lambda>t n. (\<exists>y. (\<gamma> y t n))"] by blast
  with `\<not>(\<exists>i. \<parallel>cid\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using eval_def by blast
qed    
    
subsection "Temporal Operators"
text {*
  We are now able to formalize all the rules of the calculus presented in~\cite{Marmsoler2017c}.
*}
  
subsubsection "Atomic Assertions"
text {*
  First we provide rules for basic behavior assertions.
*}

definition ass :: "('cmp \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)"
  where "ass \<phi> \<equiv> \<lambda> t n. \<phi> (t n)"
  
lemma assIA[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<phi> (\<sigma>\<^bsub>c\<^esub>(t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>))"
  shows "eval c t t' n (ass \<phi>)"
proof -
  from assms have "\<phi> (\<sigma>\<^bsub>c\<^esub>(t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>))" by simp
  moreover have "\<sigma>\<^bsub>c\<^esub>(t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>))"
  proof -
    have "enat (Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) < llength (inf_llist t)" using enat_ord_code by simp
    moreover from assms have "\<parallel>c\<parallel>\<^bsub>t (\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)\<^esub>" using nxtActI by simp
    hence "\<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" by simp
    ultimately show ?thesis using proj_active_nth by simp
  qed
  ultimately have "\<phi> (lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat(\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>)))" by simp
  moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>"
  proof -
    from assms have "\<nexists>k. n\<le>k \<and> k<\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>" using nxtActI by simp
    hence "\<not> (\<exists>k\<ge>n. k < \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) k\<^esub>)" by simp
    moreover have "enat \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
    moreover from assms have "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n" using nxtActI by simp
    ultimately show ?thesis using nAct_not_active_same[of n "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" "inf_llist t" c] by simp
  qed
  ultimately have "\<phi> (lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))" by simp
  moreover have "enat (the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)) < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
  proof -
    have "ltake \<infinity> (inf_llist t) = (inf_llist t)" using ltake_all[of "inf_llist t"] by simp
    hence "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) = \<langle>c #\<^bsub>\<infinity>\<^esub> inf_llist t\<rangle>" using nAct_def by simp
    moreover have "\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>\<infinity>\<^esub> inf_llist t\<rangle>"
    proof -
      have "enat \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> < llength (inf_llist t)" by simp
      moreover from assms have "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n" and "\<parallel>c\<parallel>\<^bsub>t (\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)\<^esub>" using nxtActI by auto
      ultimately show ?thesis using nAct_less[of "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" "inf_llist t" n \<infinity>] by simp
    qed
    ultimately show ?thesis by simp
  qed
  hence "lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) =
    lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
    using lnth_lappend1[of "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)" "\<pi>\<^bsub>c\<^esub>(inf_llist t)" "inf_llist t'"] by simp
  ultimately have "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))" by simp
  hence "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))" by simp
  moreover from assms have "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n" and "\<parallel>c\<parallel>\<^bsub>t (\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)\<^esub>" using nxtActI by auto
  ultimately have "(\<exists>i\<ge>snd (t, n). \<parallel>c\<parallel>\<^bsub>fst (t, n) i\<^esub>) \<and>
    \<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst (t, n)))) @\<^sub>l (inf_llist t'))
    (the_enat (\<langle>c #\<^bsub>the_enat (snd (t,n))\<^esub> inf_llist (fst (t, n))\<rangle>)))" by auto
  thus ?thesis using ass_def by simp
qed

lemma assIN1[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat  
  assumes act: "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and nAct: "\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and al: "\<phi> (t' (n - \<langle>c \<and> t\<rangle> - 1))"
  shows "eval c t t' n (ass \<phi>)"
proof -
  have "t' (n - \<langle>c \<and> t\<rangle> - 1) = lnth (inf_llist t') (n - \<langle>c \<and> t\<rangle> - 1)" by simp
  moreover have "\<dots> = lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n))"
    using act nAct cnf2bhv_lnth_lappend by simp
  ultimately have "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)))" using al by simp
  with act nAct show ?thesis using ass_def by simp
qed    
    
lemma assIN2[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat  
  assumes nAct: "\<nexists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and al: "\<phi> (t' n)"
  shows "eval c t t' n (ass \<phi>)"
proof -
  have "t' n = lnth (inf_llist t') n" by simp
  moreover have "\<dots> = lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n"
  proof -
    from nAct have "\<pi>\<^bsub>c\<^esub>(inf_llist t) = []\<^sub>l" by simp
    hence "(\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t') = inf_llist t'" by (simp add: \<open>\<pi>\<^bsub>c\<^esub>inf_llist t = []\<^sub>l\<close>)
    thus ?thesis by simp
  qed
  ultimately have "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n)" using al by simp
  hence "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n)" by simp
  with nAct show ?thesis using ass_def by simp
qed
  
lemma assIANow[intro]:
  fixes t n c \<phi>
  assumes "\<phi> (\<sigma>\<^bsub>c\<^esub>(t n))"
    and "\<parallel>c\<parallel>\<^bsub>t n\<^esub>"
  shows "eval c t t' n (ass \<phi>)"
proof -
  from assms have "\<phi>(\<sigma>\<^bsub>c\<^esub>(t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>))" using nxtAct_active by simp
  with assms show ?thesis using assIA by blast
qed
  
lemma assEA[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and i::nat    
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "eval c t t' n (ass \<phi>)"
  shows "\<phi> (\<sigma>\<^bsub>c\<^esub>(t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>))"
proof -
  from `eval c t t' n (ass \<phi>)` have "eval c t t' n (\<lambda> t n. \<phi> (t n))" using ass_def by simp
  moreover from assms have "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n" and "\<parallel>c\<parallel>\<^bsub>t (\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)\<^esub>" using nxtActI[of n c t] by auto
  ultimately have "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))"
    using validCE_act by blast
  hence "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))" by simp
  moreover have "enat (the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)) < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
  proof -
    have "ltake \<infinity> (inf_llist t) = (inf_llist t)" using ltake_all[of "inf_llist t"] by simp
    hence "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) = \<langle>c #\<^bsub>\<infinity>\<^esub> inf_llist t\<rangle>" using nAct_def by simp
    moreover have "\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>\<infinity>\<^esub> inf_llist t\<rangle>"
    proof -
      have "enat \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> < llength (inf_llist t)" by simp
      with `\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n` `\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>` show ?thesis using nAct_less by simp
    qed
    ultimately show ?thesis by simp
  qed
  hence "lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) =
    lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
    using lnth_lappend1[of "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)" "\<pi>\<^bsub>c\<^esub>(inf_llist t)" "inf_llist t'"] by simp
  ultimately have "\<phi> (lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))" by simp
  moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>"
  proof -
    from assms have "\<nexists>k. n\<le>k \<and> k<\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>" using nxtActI[of n c t] by auto
    hence "\<not> (\<exists>k\<ge>n. k < \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) k\<^esub>)" by simp
    moreover have "enat \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
    ultimately show ?thesis using `\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n` nAct_not_active_same by simp
  qed      
  moreover have "\<sigma>\<^bsub>c\<^esub>(t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) = lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>))"
  proof -
    have "enat (Suc i) < llength (inf_llist t)" using enat_ord_code by simp
    moreover from `\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>` have "\<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" by simp
    ultimately show ?thesis using proj_active_nth by simp
  qed
  ultimately show ?thesis by simp
qed

lemma assEN1[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat  
  assumes act: "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and nAct: "\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and al: "eval c t t' n (ass \<phi>)"
  shows "\<phi> (t' (n - \<langle>c \<and> t\<rangle> - 1))"
proof -
  from al have "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)))"
    using act nAct validCE_cont ass_def by metis
  hence "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)))" by simp
  moreover have "lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)) = lnth (inf_llist t') (n - \<langle>c \<and> t\<rangle> - 1)"
    using act nAct cnf2bhv_lnth_lappend by simp
  moreover have "\<dots> = t' (n - \<langle>c \<and> t\<rangle> - 1)" by simp
  ultimately show ?thesis by simp
qed

lemma assEN2[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat  
  assumes nAct: "\<nexists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and al: "eval c t t' n (ass \<phi>)"
  shows "\<phi> (t' n)"
proof -
  from al have "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n)"
    using nAct validCE_not_act ass_def by metis
  hence "\<phi> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n)" by simp
  moreover have "lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n = lnth (inf_llist t') n"
  proof -
    from nAct have "\<pi>\<^bsub>c\<^esub>(inf_llist t) = []\<^sub>l" by simp
    hence "(\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t') = inf_llist t'" by (simp add: \<open>\<pi>\<^bsub>c\<^esub>inf_llist t = []\<^sub>l\<close>)
    thus ?thesis by simp
  qed
  moreover have "\<dots> = t' n" by simp
  ultimately show ?thesis by simp
qed

lemma assEANow[elim]:
  fixes t n c \<phi>
  assumes "eval c t t' n (ass \<phi>)"
    and "\<parallel>c\<parallel>\<^bsub>t n\<^esub>"
  shows "\<phi> (\<sigma>\<^bsub>c\<^esub>(t n))"
proof -
  from assms have "\<phi>(\<sigma>\<^bsub>c\<^esub>(t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>))" using assEA by blast
  with assms show ?thesis using nxtAct_active by simp
qed
    
subsubsection "Next Operator"

definition nxt :: "((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" ("\<circle>(_)" 24)
  where "\<circle>(\<gamma>) \<equiv> \<lambda> t n. \<gamma> t (Suc n)"

lemma nxtIA[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<lbrakk>\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<rbrakk> \<Longrightarrow> \<exists>n' \<ge> n. (\<exists>!i. n\<le>i \<and> i<n' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> eval c t t' n' \<gamma>"
    and "\<lbrakk>\<not>(\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<rbrakk> \<Longrightarrow> eval c t t' (Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<gamma>"    
  shows "eval c t t' n (\<circle>(\<gamma>))"
proof (cases)
  assume "\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  with assms(2) obtain n' where "n'\<ge>n" and "\<exists>!i. n\<le>i \<and> i<n' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>" and "eval c t t' n' \<gamma>" by blast
  moreover from assms(1) have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n" using nxtActI by auto
  ultimately have "\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by (metis \<open>\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> dual_order.strict_trans2 leI nat_less_le)
  with `eval c t t' n' \<gamma>`
  have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>))"
    using validCE_act by blast
  moreover have "the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>) = Suc (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
  proof -
    from `\<exists>!i. n\<le>i \<and> i<n' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>` obtain i where "n\<le>i" and "i<n'" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
      and "\<forall>i'. n\<le>i' \<and> i'<n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub> \<longrightarrow> i'=i" by blast
    moreover have "n' - 1 < llength (inf_llist t)" by simp            
    ultimately have "the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>) = the_enat(eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
      using nAct_active_suc[of "inf_llist t" n' n i c]  by (simp add: \<open>n \<le> i\<close>)
    moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
    ultimately show ?thesis using the_enat_eSuc by simp
  qed    
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (Suc (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))"
    by simp
  with assms have "eval c t t' n (\<lambda>t n. \<gamma> t (Suc n))"
    using validCI_act[of n c t "\<lambda>t n. \<gamma> t (Suc n)" t'] by blast
  thus ?thesis using nxt_def by simp
next
  assume "\<not> (\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms(3) have "eval c t t' (Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<gamma>" by simp
  moreover from `\<not> (\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<not> (\<exists>i\<ge>Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)" by simp
  ultimately have "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>))"
    using assms(1) validCE_cont[of c t "Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" t' \<gamma>] by blast
  moreover from assms(1) `\<not> (\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)`
    have "Suc (the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>) = \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)"
    using nAct_cnf2proj_Suc_dist by simp
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (Suc (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))"
    by simp
  moreover from assms(1) have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n" using nxtActI by auto
  ultimately have "eval c t t' n (\<lambda>t n. \<gamma> t (Suc n))" using validCI_act[of n c t "\<lambda>t n. \<gamma> t (Suc n)" t']
    by blast
  with `\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>` `\<not> (\<exists>i'\<ge>Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` show ?thesis using nxt_def by simp
qed
  
lemma nxtIN[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat  
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "eval c t t' (Suc n) \<gamma>"
  shows "eval c t t' n (\<circle>(\<gamma>))"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  moreover from `\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<not> (\<exists>i\<ge>Suc n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)" by simp
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(Suc n))"
    using validCE_cont `eval c t t' (Suc n) \<gamma>` by blast
  with \<open>\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (Suc (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)))"
    using `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` lActive_less by auto
  with `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "eval c t t' n (\<lambda>t n. \<gamma> t (Suc n))"
    using validCI_cont[where \<gamma>="(\<lambda>t n. \<gamma> t (Suc n))"] by simp
  thus ?thesis using nxt_def by simp
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms have "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) (Suc n)" using validCE_not_act by blast
  with `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "eval c t t' n (\<lambda>t n. \<gamma> t (Suc n))"
    using validCI_not_act[where \<gamma>="(\<lambda>t n. \<gamma> t (Suc n))"] by blast
  thus ?thesis using nxt_def by simp
qed
  
lemma nxtEA1[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
  assumes "\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "eval c t t' n (\<circle>(\<gamma>))"
    and "n'\<ge>n"
    and "\<exists>!i. i\<ge>n \<and> i<n' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "eval c t t' n' \<gamma>"
proof -
  from `eval c t t' n (\<circle>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<gamma> t (Suc n))" using nxt_def by simp
  moreover from assms(4) obtain i where "i\<ge>n" and "i<n'" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>i'. n\<le>i' \<and> i'<n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub> \<longrightarrow> i'=i" by blast
  ultimately have "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) (Suc (the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>))"
    using validCE_act[of n c t t' "\<lambda>t n. \<gamma> t (Suc n)"] by blast
  moreover have "the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>) = Suc (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
  proof -
    have "n' - 1 < llength (inf_llist t)" by simp            
    with `i<n'` and `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` and `\<forall>i'. n\<le>i' \<and> i'<n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub> \<longrightarrow> i'=i`
      have "the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>) = the_enat(eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
      using nAct_active_suc[of "inf_llist t" n' n i c]  by (simp add: \<open>n \<le> i\<close>)
    moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
    ultimately show ?thesis using the_enat_eSuc by simp
  qed    
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>inf_llist t) @\<^sub>l inf_llist t')) (the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>))" by simp
  moreover have "\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
  proof -
    from assms(4) have "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n" and "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by auto
    with `\<forall>i'. n\<le>i' \<and> i'<n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub> \<longrightarrow> i'=i` show ?thesis
      using assms(1) by (metis leI le_trans less_le)
  qed
  ultimately show ?thesis using validCI_act by blast
qed
  
lemma nxtEA2[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and "i"
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" and "\<not>(\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "eval c t t' n (\<circle>(\<gamma>))"
  shows "eval c t t' (Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>) \<gamma>"
proof -
  from `eval c t t' n (\<circle>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<gamma> t (Suc n))" using nxt_def by simp
  with assms(1) have "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) (Suc (the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>))"
    using validCE_act[of n c t t' "\<lambda>t n. \<gamma> t (Suc n)"] by blast
  moreover from assms(1) assms(2) have "Suc (the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)=\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)"
    using nAct_cnf2proj_Suc_dist by simp
  ultimately have "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>))" by simp
  moreover from assms(1) assms(2) have "\<not>(\<exists>i'\<ge>Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
    using nxtActive_no_active by simp
  ultimately show ?thesis using validCI_cont[where n="Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] assms(1) by blast
qed

lemma NxtEN[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat 
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "eval c t t' n (\<circle>(\<gamma>))"
  shows "eval c t t' (Suc n) \<gamma>"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  moreover from `eval c t t' n (\<circle>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<gamma> t (Suc n))" using nxt_def by simp
  ultimately have "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) (Suc (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>n))"
    using `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` validCE_cont[where \<gamma>="(\<lambda>t n. \<gamma> t (Suc n))"] by simp
  hence "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(Suc n))"
    using \<open>\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> assms(1) lActive_less by auto
  moreover from `\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<not> (\<exists>i\<ge>Suc n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)" by simp      
  ultimately show ?thesis using validCI_cont[where n="Suc n"] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval c t t' n (\<circle>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<gamma> t (Suc n))" using nxt_def by simp
  ultimately have "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) (Suc n)"
    using `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` validCE_not_act[where \<gamma>="(\<lambda>t n. \<gamma> t (Suc n))"] by blast
  with `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using validCI_not_act[of c t \<gamma> t' "Suc n"] by blast
qed

subsubsection "Eventually Operator"  

definition evt :: "((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" ("\<diamond>(_)" 23)
  where "\<diamond>(\<gamma>) \<equiv> \<lambda> t n. \<exists>n'\<ge>n. \<gamma> t n'"

lemma evtIA[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and n'::nat
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "n'\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
    and "\<lbrakk>\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<rbrakk> \<Longrightarrow> \<exists>n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n''\<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<and> eval c t t' n'' \<gamma>"
    and "\<lbrakk>\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<rbrakk> \<Longrightarrow> eval c t t' n' \<gamma>"    
  shows "eval c t t' n (\<diamond>(\<gamma>))"
proof cases  assume "\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
  with assms(3) obtain n'' where "n'' \<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>" and "n''\<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n'\<^esub>" and "eval c t t' n'' \<gamma>" by auto
  hence "\<exists>i'\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" using \<open>\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>\<close> nxtActI by blast
  with `eval c t t' n'' \<gamma>` have
    "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>))"
    using validCE_act by blast
  moreover have "the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>) \<le> the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>)"
  proof -
    from `\<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>\<le>n''` have "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>"
      using nAct_mono_lNact by simp
    moreover from `n'\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>` have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>"
      using nAct_mono_lNact by simp
    moreover have "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
    ultimately show ?thesis by simp
  qed
  moreover have "\<exists>i'\<ge>n. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
  proof -
    from `\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>` obtain i' where "i'\<ge>n'" and "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by blast
    with `n'\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>` have "i'\<ge> n" using lNactGe le_trans by blast
    with `\<parallel>c\<parallel>\<^bsub>t i'\<^esub>` show ?thesis by blast
  qed
  ultimately have "eval c t t' n (\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')"
    using validCI_act[where \<gamma>="(\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')"] by blast
  thus ?thesis using evt_def by simp
next
  assume "\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
  with `(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "n' \<ge> \<langle>c \<and> t\<rangle>" using lActive_less by auto
  hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" using cnf2bhv_ge_llength by simp
  moreover have "the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 \<ge> the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
  proof -
    from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) \<ge> eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
      using nAct_llength_proj by simp
    moreover from `\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
      using proj_finite2[of "inf_llist t"] by simp
    hence "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>" using llength_eq_infty_conv_lfinite by auto
    ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) \<ge> the_enat(eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
      by simp
    moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
    ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) \<ge> Suc (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
      using the_enat_eSuc by simp
    thus ?thesis by simp
  qed
  ultimately have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by simp   
  moreover from `\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "eval c t t' n' \<gamma>" using assms(4) by simp
    with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)`
    have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))" using validCE_cont by blast
  ultimately have "eval c t t' n (\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')"
    using `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validCI_act[where \<gamma>="(\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')"] by blast
  thus ?thesis using evt_def by simp
qed
    
lemma evtIN[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and n'::nat
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "n'\<ge>n"
    and "eval c t t' n' \<gamma>"
  shows "eval c t t' n (\<diamond>(\<gamma>))"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  moreover from assms(1) assms(2) have "\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)" by simp
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))"
    using validCE_cont[of c t n' t' \<gamma>] `eval c t t' n' \<gamma>` by blast
  moreover from `n'\<ge>n` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" using cnf2bhv_mono by simp
  ultimately have "eval c t t' n (\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')"
    using validCI_cont[where \<gamma>="(\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')"] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` by blast
  thus ?thesis using evt_def by simp
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms have "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'" using validCE_not_act by blast
  with `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "eval c t t' n (\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')"
    using validCI_not_act[where \<gamma>="\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n'"] `n'\<ge>n` by blast
  thus ?thesis using evt_def by simp
qed
  
lemma evtEA[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat  
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "eval c t t' n (\<diamond>(\<gamma>))"
  shows "\<exists>n'\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>.
          (\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub> \<and> (\<forall>n''\<ge> \<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> eval c t t' n'' \<gamma>)) \<or>
          (\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> eval c t t' n' \<gamma>)"
proof -
  from `eval c t t' n (\<diamond>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')" using evt_def by simp
  with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
    have "\<exists>n'\<ge>the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'"
    using validCE_act[where \<gamma>="\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n'"] by blast
  then obtain x where "x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" and
    "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x" by auto
  thus ?thesis
  proof (cases)
    assume "x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
    moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>"
      by (metis infinity_ileE)
    moreover from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<ge>1"
      using proj_one[of "inf_llist t"] by auto
    ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x"
      by (metis One_nat_def Suc_ile_eq antisym_conv2 diff_Suc_less enat_ord_simps(2)
          enat_the_enat less_imp_diff_less one_enat_def)
    hence "x = \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x))" using cnf2bhv_bhv2cnf by simp
    with `\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x`
      have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)))" by simp
    moreover have "\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    proof -
      from `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
      then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
      moreover from `the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x` have "\<langle>c \<and> t\<rangle> < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)"
        using bhv2cnf_greater_lActive by simp
      ultimately show ?thesis using lActive_greater_active_all by simp
    qed
    ultimately have "eval c t t' (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x) \<gamma>"
      using `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validCI_cont[of c t "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)"] by blast
    moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
    proof -
      from `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
      then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
      moreover from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by simp
      ultimately have "\<langle>c \<and> t\<rangle>\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using lActive_greatest by fastforce
      moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<and> t\<rangle>" by simp
      ultimately show "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" by arith
    qed
    ultimately show ?thesis using `\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` by blast
  next
    assume "\<not>(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
    hence "x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" by simp
    then obtain n'::nat where "x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_exists by blast
    with \<open>enat x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close> have "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active by force
    then obtain i where "i\<ge>n'" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>" and "\<not> (\<exists>k\<ge>n'. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)" using nact_exists by blast
    moreover have "(\<forall>n''\<ge> \<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>. n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub> \<longrightarrow> eval c t t' n'' \<gamma>)"
    proof
      fix n'' show "\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub> \<le> n'' \<longrightarrow> n'' \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub> \<longrightarrow> eval c t t' n'' \<gamma>"
      proof(rule HOL.impI[OF HOL.impI])
        assume "\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub> \<le> n''" and "n'' \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>"
        hence "the_enat (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>) = the_enat (\<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>)"
          using nAct_same by simp
        moreover from `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>\<^esub>" using nxtActI by auto
        with `n'' \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>` have "\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using dual_order.strict_implies_order by auto
        moreover have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>))"
        proof -
          have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
          with `x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>` `i\<ge>n'` `\<not> (\<exists>k\<ge>n'. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)` have "x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>"
            using one_enat_def nAct_not_active_same by simp
          moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
          ultimately have "x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" by fastforce        
          thus ?thesis using `\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x` by blast
        qed
        with `the_enat (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>) = the_enat (\<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>)` have
          "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>))" by simp
        ultimately show "eval c t t' n'' \<gamma>" using validCI_act by blast
      qed
    qed
    moreover have "i\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
    proof -
      have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
      with `x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>` `i\<ge>n'` `\<not> (\<exists>k\<ge>n'. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)` have "x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>"
        using one_enat_def nAct_not_active_same by simp
      moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
      ultimately have "x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" by fastforce        
      with `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)`
        have "the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by simp
      with `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using active_geq_nxtAct by simp
    qed
    ultimately show ?thesis using `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` by auto
  qed    
qed
    
lemma evtEN[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and n'::nat  
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "eval c t t' n (\<diamond>(\<gamma>))"
  shows "\<exists>n'\<ge>n. eval c t t' n' \<gamma>" 
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  moreover from `eval c t t' n (\<diamond>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')" using evt_def by simp
  ultimately have "\<exists>n'\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>n. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'"
    using validCE_cont[where \<gamma>="(\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')"] `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` by blast
  then obtain x where "x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" and " \<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x" by auto
  moreover have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x"
  proof -
    have "\<langle>c \<and> t\<rangle> < n"
    proof (rule ccontr)
      assume "\<not>\<langle>c \<and> t\<rangle> < n"
      hence "\<langle>c \<and> t\<rangle> \<ge> n" by simp
      moreover from \<open>\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<and> t\<rangle>\<^esub>"
        using lActive_active less_or_eq_imp_le by blast
      ultimately show False using \<open>\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> by simp
    qed
    hence "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" using cnf2bhv_greater_llength by simp
    with `x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)` show ?thesis by simp
  qed
  hence "x = \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x))" using cnf2bhv_bhv2cnf by simp
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)))" by simp
  moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  proof -
    from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using proj_finite2 by simp
    then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
    moreover from `the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x` have "\<langle>c \<and> t\<rangle> < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)"
      using bhv2cnf_greater_lActive by simp
    ultimately show ?thesis using lActive_greater_active_all by simp
  qed      
  ultimately have "eval c t t' (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x) \<gamma>"
    using validCI_cont[of c t "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)" \<gamma>] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
  moreover from `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using lActive_less[of c t _ n] by auto
  with `x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)` have "n \<le> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)" using p2c_mono_c2p by blast  
  ultimately show ?thesis by auto
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval c t t' n (\<diamond>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n')" using evt_def by simp
  ultimately obtain n' where "n'\<ge>n" and "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'"
    using `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` validCE_not_act[where \<gamma>="\<lambda>t n. \<exists>n'\<ge>n. \<gamma> t n'"] by blast
  with `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using validCI_not_act[of c t \<gamma> t' n'] by blast
qed    

subsubsection "Globally Operator"

definition glob :: "((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" ("\<box>(_)" 22)
  where "\<box>(\<gamma>) \<equiv> \<lambda> t n. \<forall>n'\<ge>n. \<gamma> t n'"
    
lemma globIA[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat  
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<And>n'. \<lbrakk>\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>; n'\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<rbrakk> \<Longrightarrow> \<exists>n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<and> eval c t t' n'' \<gamma>"
    and "\<And>n'. \<lbrakk>\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>); n'\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<rbrakk> \<Longrightarrow> eval c t t' n' \<gamma>" 
  shows "eval c t t' n (\<box>(\<gamma>))"
proof -
  have "\<forall>n'\<ge>the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'"
  proof
    fix x::nat show
      "x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>) \<longrightarrow> \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
    proof
      assume "x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
      show "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x"
      proof (cases)
        assume "(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
        hence "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
          using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
        then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
        moreover have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" by (simp add: \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> nxtActI)
        ultimately have "\<langle>c \<and> t\<rangle>\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using lActive_greatest[of c t "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by blast
        moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<and> t\<rangle>" by simp
        ultimately have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" by arith
        moreover have "\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
        proof -
          from `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
            have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) = Suc (\<langle>c \<and> t\<rangle>)"
            using bhv2cnf_lActive by blast
          moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))` have "x \<ge> the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
            using the_enat_mono by fastforce
          hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))))"
            using bhv2cnf_mono[of "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" x] by simp
          ultimately have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> Suc (\<langle>c \<and> t\<rangle>)" by simp
          hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) > \<langle>c \<and> t\<rangle>" by simp
          with `\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>` show ?thesis using lActive_greater_active_all by simp
        qed
        ultimately have "eval c t t' (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)) \<gamma>" using assms(3) by simp
        hence "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)))"
          using validCE_cont[of c t "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)" t' \<gamma>] `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` by blast
        moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))`
          have "(enat x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" by auto
        with `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>"
          using llength_eq_infty_conv_lfinite by auto
        with `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))`
          have "the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 \<le> x" by auto
        ultimately show ?thesis using cnf2bhv_bhv2cnf[of c t x] by simp
      next
        assume "\<not>(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
        hence "x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" by simp
        then obtain n'::nat where "x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_exists by blast
        moreover from \<open>enat x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close> \<open>enat x = \<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>\<close>
          have "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active by force
        then obtain i where "i\<ge>n'" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>" and "\<not> (\<exists>k\<ge>n'. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
          using nact_exists by blast
        moreover have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
        ultimately have "x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>" using one_enat_def nAct_not_active_same by simp
        moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
        ultimately have "x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" by fastforce
        from `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)` `x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)`
        have "the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by simp
        with `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "i\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using active_geq_nxtAct by simp
        moreover from `x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>` `x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))`
          have "\<exists>i'. i \<le> enat i' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" using nAct_less_llength_active[of x c "inf_llist t" i] by simp
        hence "\<exists>i'\<ge>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by simp
        ultimately obtain n'' where "eval c t t' n'' \<gamma>" and "n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>" and "n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>"
          using assms(2) by blast
        moreover have "\<exists>i'\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
          using \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> `n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>` less_or_eq_imp_le nxtAct_active by auto
        ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>))"
          using validCE_act[of n'' c t t' \<gamma>] by blast
        moreover from `n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>` and `n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>`
          have "the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>)=the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" using nAct_same by simp
        hence "the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) = x" by (simp add: \<open>x = the_enat \<langle>c #\<^bsub>enat i\<^esub>inf_llist t\<rangle>\<close>)
        ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat x)" by simp
        thus ?thesis by simp
      qed
    qed
  qed
  with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "eval c t t' n (\<lambda>t n. \<forall>n'\<ge>n. \<gamma> t n')"
    using validCI_act[of n c t "\<lambda> t n. \<forall>n'\<ge>n. \<gamma> t n'" t'] by blast
  thus ?thesis using glob_def by simp
qed
  
lemma globIN[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat  
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "\<And>n'. n'\<ge>n \<Longrightarrow> eval c t t' n' \<gamma>"
  shows "eval c t t' n (\<box>(\<gamma>))"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"    
  from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using proj_finite2 by simp
  then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
    
  have "\<forall>x::nat\<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n). \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
  proof
    fix x::nat show "(x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)) \<longrightarrow> \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
    proof
      assume "x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)"
      moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` lActive_less by auto
      ultimately have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> n" using p2c_mono_c2p by simp
      with assms have "eval c t t' (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)) \<gamma>" by simp    
      moreover have "\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
      proof -
        from `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
          have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) = Suc (\<langle>c \<and> t\<rangle>)"
          using bhv2cnf_lActive by blast
        moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "n>\<langle>c \<and> t\<rangle>"
          by (meson `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` lActive_active leI le_eq_less_or_eq)
        hence "n\<ge>Suc (\<langle>c \<and> t\<rangle>)" by simp
        with `n\<ge>Suc(\<langle>c \<and> t\<rangle>)` `\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> n` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> Suc (\<langle>c \<and> t\<rangle>)" by simp
        hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) > \<langle>c \<and> t\<rangle>" by simp
        with `\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>` show ?thesis using lActive_greater_active_all by simp
      qed
      ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)))"
        using validCE_cont[of c t "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)" t' \<gamma>] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
      moreover have "x \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
        using \<open>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) \<le> x\<close> cnf2bhv_def by auto
      ultimately show "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x"
        using cnf2bhv_bhv2cnf by simp
    qed
  qed
  with `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "eval c t t' n (\<lambda>t n. \<forall>n'\<ge>n. \<gamma> t n')"
    using validCI_cont[of c t n "\<lambda> t n. \<forall>n'\<ge>n. \<gamma> t n'" t'] by simp
  thus ?thesis using glob_def by simp
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms have "\<forall>n'\<ge>n. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'" using validCE_not_act by blast
  with `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "eval c t t' n (\<lambda>t n. \<forall>n'\<ge>n. \<gamma> t n')"
    using validCI_not_act[where \<gamma>="\<lambda> t n. \<forall>n'\<ge>n. \<gamma> t n'"] by blast
  thus ?thesis using glob_def by simp
qed
      
lemma globEA[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and n'::nat
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "eval c t t' n (\<box>(\<gamma>))"
    and "n'\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
  shows "eval c t t' n' \<gamma>"
proof (cases)
  assume "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  with `n'\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>` have "the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>) \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
    using nAct_mono_lNact `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
  moreover from `eval c t t' n (\<box>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<forall>n'\<ge>n. \<gamma> t n')"
    using glob_def by simp
  hence "\<forall>x\<ge>the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
    using validCE_act `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>))" by simp
  with `\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using validCI_act by blast    
next
  assume "\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  from `eval c t t' n (\<box>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<forall>n'\<ge>n. \<gamma> t n')" using glob_def by simp
  hence "\<forall>x\<ge>the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
    using validCE_act `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
  moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
  proof -
    have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>\<le>llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using nAct_le_proj by metis
    moreover from \<open>\<not> (\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>"
      by (metis llength_eq_infty_conv_lfinite lnth_inf_llist proj_finite2)
    ultimately have "the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)\<le>the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" by simp
    moreover from \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<not> (\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> have "n'>\<langle>c \<and> t\<rangle>"
      using lActive_active by (meson leI le_eq_less_or_eq)
    hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') > the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" using cnf2bhv_greater_llength by simp
    ultimately show ?thesis by simp
  qed
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))" by simp
  with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using validCI_cont by blast
qed

lemma globEANow:
  fixes c t t' n i \<gamma>
  assumes "n \<le> i"
    and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "eval c t t' n (\<box>\<gamma>)"
  shows "eval c t t' i \<gamma>"
proof -
  from \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>n \<le> i\<close> have "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by auto
  moreover from \<open>n \<le> i\<close> have "\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> i" using dual_order.trans lNactLe by blast
  ultimately show ?thesis using globEA[of n c t t' \<gamma> i] \<open>eval c t t' n (\<box>\<gamma>)\<close> by simp
qed

lemma globEN[elim]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and n'::nat
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "eval c t t' n (\<box>(\<gamma>))"
    and "n'\<ge>n"
  shows "eval c t t' n' \<gamma>"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  moreover from `eval c t t' n (\<box>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<forall>n'\<ge>n. \<gamma> t n')"
    using glob_def by simp
  ultimately have "\<forall>x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>n. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
    using validCE_cont[of c t n t' "\<lambda>t n. \<forall>n'\<ge>n. \<gamma> t n'"] `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` by blast
  moreover from `n'\<ge>n` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" using cnf2bhv_mono by simp
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))" by simp
  moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` `n'\<ge>n` have "\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)" by simp
  ultimately show ?thesis using validCI_cont `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval c t t' n (\<box>(\<gamma>))` have "eval c t t' n (\<lambda>t n. \<forall>n'\<ge>n. \<gamma> t n')"
    using glob_def by simp
  ultimately have "\<forall>n'\<ge>n. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'"
    using `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` validCE_not_act[where \<gamma>="\<lambda>t n. \<forall>n'\<ge>n. \<gamma> t n'"] by blast
  with `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` `n'\<ge>n` show ?thesis using validCI_not_act by blast
qed

subsubsection "Until Operator"

definition until :: "((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)
  \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" (infixl "\<UU>" 21)
  where "\<gamma>' \<UU> \<gamma> \<equiv> \<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')"
    
lemma untilIA[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and n'::nat
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "n'\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
    and "\<lbrakk>\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<rbrakk> \<Longrightarrow> \<exists>n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n''\<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<and> eval c t t' n'' \<gamma> \<and>
      (\<forall>n'''\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. n'''< \<langle>c \<leftarrow> t\<rangle>\<^bsub>n''\<^esub>
      \<longrightarrow> (\<exists>n''''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n'''\<^esub>. n''''\<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n'''\<^esub> \<and> eval c t t' n'''' \<gamma>'))"
    and "\<lbrakk>\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<rbrakk> \<Longrightarrow> eval c t t' n' \<gamma> \<and>
      (\<forall>n''\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. n''< n'
      \<longrightarrow> ((\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> (\<exists>n'''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n''\<^esub>. n'''\<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n''\<^esub> \<and> eval c t t' n''' \<gamma>')) \<or>
      (\<not>(\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> eval c t t' n'' \<gamma>'))"
  shows "eval c t t' n (\<gamma>' \<UU> \<gamma>)"
proof cases
  assume "\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
  with assms(3) obtain n'' where "n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>" and "n''\<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n'\<^esub>" and "eval c t t' n'' \<gamma>" and
    a1: "\<forall>n'''\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. n'''< \<langle>c \<leftarrow> t\<rangle>\<^bsub>n''\<^esub>
    \<longrightarrow> (\<exists>n''''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n'''\<^esub>. n''''\<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n'''\<^esub> \<and> eval c t t' n'''' \<gamma>')" by blast
  hence "\<exists>i'\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" using \<open>\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>\<close> nxtActI by blast
  with `eval c t t' n'' \<gamma>` have
    "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>))"
    using validCE_act by blast
  moreover have "the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>) \<le> the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>)"
  proof -
    from `\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<le>n'` have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>"
      using nAct_mono_lNact by simp
    moreover from `\<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>\<le>n''` have "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>"
      using nAct_mono_lNact by simp        
    ultimately have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>" by simp
    moreover have "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
    ultimately show ?thesis by simp
  qed
  moreover have "\<exists>i'\<ge>n. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
  proof -
    from `\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>` obtain i' where "i'\<ge>n'" and "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by blast
    with `n'\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>` have "i'\<ge> n" using lNactGe le_trans by blast
    with `\<parallel>c\<parallel>\<^bsub>t i'\<^esub>` show ?thesis by blast
  qed
  moreover have "\<forall>n'\<ge>the_enat \<langle>c #\<^bsub>n\<^esub>inf_llist t\<rangle>. n' < (the_enat \<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle>)
    \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'"
  proof
    fix x::nat show "x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)
      \<longrightarrow> x < (the_enat \<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle>) \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
    proof (rule HOL.impI[OF HOL.impI])
      assume "x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" and "x < (the_enat \<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle>)"
      moreover have "the_enat (\<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>) = \<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>" by simp
      ultimately have "x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using nAct_le_proj[of c n'' "inf_llist t"]
        by (metis enat_ord_simps(2) less_le_trans)
      hence "x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" by simp
      then obtain n'::nat where "x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_exists by blast
      moreover from \<open>enat x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close> \<open>enat x = \<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>\<close>
        have "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active by force
      then obtain i where "i\<ge>n'" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>" and "\<not> (\<exists>k\<ge>n'. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)" using nact_exists by blast
      moreover have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
      ultimately have "x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>" using one_enat_def nAct_not_active_same by simp
      moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
      ultimately have "x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" by fastforce
      from `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)` `x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)`
      have "the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by simp
      with `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "i\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using active_geq_nxtAct by simp
      moreover have "i < \<langle>c \<leftarrow> t\<rangle>\<^bsub>n''\<^esub>"
      proof -
        have "the_enat \<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle> = \<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle>" by simp
        with `x < (the_enat \<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle>)` and `x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>` have
          "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle><\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>" by (metis enat_ord_simps(2))
        hence "i<n''" using nAct_strict_mono_back[of c i "inf_llist t" n''] by auto
        with `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using lNact_notActive leI by blast
      qed
      ultimately obtain n'' where "eval c t t' n'' \<gamma>'" and "n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>" and "n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>"
        using a1 by auto
      moreover have "\<exists>i'\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
        using \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> `n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>` less_or_eq_imp_le nxtAct_active by auto
      ultimately have "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>))"
        using validCE_act[of n'' c t t' \<gamma>'] by blast
      moreover from `n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>` and `n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>`
        have "the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>)=the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" using nAct_same by simp
      hence "the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) = x" by (simp add: \<open>x = the_enat \<langle>c #\<^bsub>enat i\<^esub>inf_llist t\<rangle>\<close>)
      ultimately show "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x" by simp
    qed
  qed 
  ultimately have "eval c t t' n (\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n'))"
    using validCI_act[where \<gamma>="\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')"] by blast
  thus ?thesis using until_def by simp
next
  assume "\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
  with assms(4) have "eval c t t' n' \<gamma>" and a2: "\<forall>n''\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. n''< n'
    \<longrightarrow> ((\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> (\<exists>n'''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n''\<^esub>. n'''\<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n''\<^esub> \<and> eval c t t' n''' \<gamma>')) \<or>
    (\<not>(\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> eval c t t' n'' \<gamma>')" by auto
  with `\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` `eval c t t' n' \<gamma>` `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have
    "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))" using validCE_cont by blast
  moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
  proof -
    from `(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` `\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "n' \<ge> \<langle>c \<and> t\<rangle>" using lActive_less by auto
    hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" using cnf2bhv_ge_llength by simp
    moreover have "the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 \<ge> the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
    proof -
      from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) \<ge> eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
        using nAct_llength_proj by simp
      moreover from `\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using proj_finite2[of "inf_llist t"] by simp
      hence "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>" using llength_eq_infty_conv_lfinite by auto
      ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) \<ge> the_enat(eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
        by simp
      moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
      ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) \<ge> Suc (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
        using the_enat_eSuc by simp
      thus ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
  moreover have "\<forall>x\<ge>the_enat \<langle>c #\<^bsub>n\<^esub>inf_llist t\<rangle>. x < (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))
    \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
  proof
    fix x::nat show
      "x\<ge>the_enat \<langle>c #\<^bsub>n\<^esub>inf_llist t\<rangle> \<longrightarrow> x < (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n')) \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
    proof (rule HOL.impI[OF HOL.impI])
      assume "x\<ge>the_enat \<langle>c #\<^bsub>n\<^esub>inf_llist t\<rangle>" and "x < (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))"
      show "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x"
      proof (cases)
        assume "(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
        hence "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
          using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
        then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
        moreover have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" by (simp add: \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> nxtActI)
        ultimately have "\<langle>c \<and> t\<rangle>\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using lActive_greatest[of c t "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by blast
        moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<and> t\<rangle>" by simp
        ultimately have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" by arith
        moreover have "\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
        proof -
          from `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
            have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) = Suc (\<langle>c \<and> t\<rangle>)"
            using bhv2cnf_lActive by blast
          moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))` have "x \<ge> the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
            using the_enat_mono by fastforce
          hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))))"
            using bhv2cnf_mono[of "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" x] by simp
          ultimately have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> Suc (\<langle>c \<and> t\<rangle>)" by simp
          hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) > \<langle>c \<and> t\<rangle>" by simp
          with `\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>` show ?thesis using lActive_greater_active_all by simp
        qed
        moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x < n'"
        proof -
          from `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "llength (\<pi>\<^bsub>c\<^esub>inf_llist t) = the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t))"
            by (simp add: enat_the_enat llength_eq_infty_conv_lfinite)
          with `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "x\<ge>the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t))"
            using enat_ord_simps(1) by fastforce
          moreover from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "llength (\<pi>\<^bsub>c\<^esub>inf_llist t)\<ge>1" using proj_one by force
          ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) - 1 \<le> x" by simp
          with `x < (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))` show ?thesis using c2p_mono_p2c_strict by simp
        qed
        ultimately have "eval c t t' (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)) \<gamma>'" using a2 by blast
        hence "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)))"
          using validCE_cont[of c t "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)" t' \<gamma>'] `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` by blast
        moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))`
          have "(enat x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" by auto
        with `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>"
          using llength_eq_infty_conv_lfinite by auto
        with `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))`
          have "the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 \<le> x" by auto
        ultimately show ?thesis using cnf2bhv_bhv2cnf[of c t x] by simp
      next
        assume "\<not>(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
        hence "x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" by simp
        then obtain n''::nat where "x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>" using nAct_exists by blast
        moreover from \<open>enat x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close> \<open>enat x = \<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>\<close>
          have "\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active by force
        then obtain i where "i\<ge>n''" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>" and "\<not> (\<exists>k\<ge>n''. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)" 
          using nact_exists by blast
        moreover have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
        ultimately have "x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>" using one_enat_def nAct_not_active_same by simp
        moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
        ultimately have "x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" by fastforce
        from `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)` `x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)`
        have "the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by simp
        with `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "i\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using active_geq_nxtAct by simp
        moreover from `x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>` `x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))`
          have "\<exists>i'. i \<le> enat i' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" using nAct_less_llength_active[of x c "inf_llist t" i] by simp
        hence "\<exists>i'\<ge>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by simp
        moreover have "i<n'"
        proof -
          from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "n'\<ge>\<langle>c \<and> t\<rangle>" using lActive_less by auto
          hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n')\<ge>the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" using cnf2bhv_ge_llength by simp
          with `x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` show ?thesis
            using \<open>\<not> (\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)\<close> \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> le_neq_implies_less nat_le_linear by blast
        qed
        ultimately obtain n''' where "eval c t t' n''' \<gamma>'" and "n'''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>" and "n'''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>"
          using a2 by blast
        moreover from `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>\<^esub>" using nxtActI by auto
        with `n'''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>` have "\<exists>i'\<ge>n'''. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" using less_or_eq_imp_le by blast
        ultimately have "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>n'''\<^esub> inf_llist t\<rangle>))"
          using validCE_act[of n''' c t t' \<gamma>'] by blast
        moreover from `n'''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>` and `n'''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>`
          have "the_enat (\<langle>c #\<^bsub>n'''\<^esub> inf_llist t\<rangle>)=the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" using nAct_same by simp
        hence "the_enat (\<langle>c #\<^bsub>n'''\<^esub> inf_llist t\<rangle>) = x" by (simp add: \<open>x = the_enat \<langle>c #\<^bsub>enat i\<^esub>inf_llist t\<rangle>\<close>)
        ultimately have "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat x)" by simp
        thus ?thesis by simp
      qed
    qed
  qed
  ultimately have "eval c t t' n (\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n'))"
    using `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validCI_act[of n c t "\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')" t']
    by blast
  thus ?thesis using until_def by simp
qed
  
lemma untilIN[intro]:
  fixes c::'id
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and n'::nat
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "n'\<ge>n"
    and "eval c t t' n' \<gamma>"
    and a1: "\<And>n''. \<lbrakk>n\<le>n''; n''<n'\<rbrakk> \<Longrightarrow> eval c t t' n'' \<gamma>'"
  shows "eval c t t' n (\<gamma>' \<UU> \<gamma>)"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  moreover from assms(1) assms(2) have "\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)" by simp
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))"
    using validCE_cont[of c t n' t' \<gamma>] `eval c t t' n' \<gamma>` by blast
  moreover from `n'\<ge>n` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" using cnf2bhv_mono by simp
  moreover have "\<forall>x::nat\<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n). x<\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<longrightarrow> \<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x"
  proof (rule HOL.allI[OF HOL.impI[OF HOL.impI]])
    fix x assume "x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" and "x<\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n')"
  
    from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` lActive_less by auto
    with `x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> n" using p2c_mono_c2p by simp
    moreover from `\<langle>c \<and> t\<rangle> \<le> n` \<open>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) \<le> x\<close> have "x \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
      using cnf2bhv_ge_llength dual_order.trans by blast
    with `x<\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n')` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) < n'" using c2p_mono_p2c_strict[of c t x n'] by simp
    moreover from \<open>\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> `\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> n` have "\<not> (\<exists>i''\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i''\<^esub>)" by auto
    ultimately have "eval c t t' (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)) \<gamma>'" using a1[of "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)"] by simp
    with \<open>\<not> (\<exists>i''\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x. \<parallel>c\<parallel>\<^bsub>t i''\<^esub>)\<close>
      have "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)))"
      using validCE_cont[of c t "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)" t' \<gamma>'] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
    moreover have "x \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
      using \<open>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) \<le> x\<close> cnf2bhv_def by auto
    ultimately show "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (x)"
      using cnf2bhv_bhv2cnf by simp
  qed   
  ultimately have "eval c t t' n (\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n'))"
    using validCI_cont[of c t n "\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')" t']
    `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i'\<ge>n. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` by blast
  thus ?thesis using until_def by simp
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms have "\<exists>n''\<ge>n. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'' \<and>
    (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n')" using validCE_not_act by blast
  with `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "eval c t t' n (\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n'))"
    using validCI_not_act[where \<gamma>="\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')"] by blast
  thus ?thesis using until_def by simp
qed
  
lemma untilEA[elim]:
  fixes n::nat
    and n'::nat
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and c::'id
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "eval c t t' n (\<gamma>' \<UU> \<gamma>)"
  shows "\<exists>n'\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>.
    ((\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> (\<forall>n''\<ge> \<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> eval c t t' n'' \<gamma>)
      \<and> (\<forall>n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'' < \<langle>c \<leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> eval c t t' n'' \<gamma>') \<or>
    (\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)) \<and> eval c t t' n' \<gamma> \<and> (\<forall>n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'' < n' \<longrightarrow> eval c t t' n'' \<gamma>'))"
proof -
  from `eval c t t' n (\<gamma>' \<UU> \<gamma>)`
    have "eval c t t' n (\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n'))" using until_def by simp
  with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` obtain x
    where "x\<ge>the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>" and "\<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x"
    and a1: "\<forall>x'\<ge>the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>. x' < x \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) x'"
    using validCE_act[where \<gamma>="\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')"] by blast
  thus ?thesis
  proof (cases)
    assume "x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
    moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>"
      by (metis infinity_ileE)
    moreover from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<ge>1"
      using proj_one[of "inf_llist t"] by auto
    ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x"
      by (metis One_nat_def Suc_ile_eq antisym_conv2 diff_Suc_less enat_ord_simps(2)
          enat_the_enat less_imp_diff_less one_enat_def)
    hence "x = \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x))" using cnf2bhv_bhv2cnf by simp
    with `\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x`
      have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)))" by simp
    moreover have "\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    proof -
      from `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
      then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
      moreover from `the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x` have "\<langle>c \<and> t\<rangle> < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)"
        using bhv2cnf_greater_lActive by simp
      ultimately show ?thesis using lActive_greater_active_all by simp
    qed
    ultimately have "eval c t t' (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x) \<gamma>"
      using `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validCI_cont[of c t "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)"] by blast
    moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
    proof -
      from `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
      then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
      moreover from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by simp
      ultimately have "\<langle>c \<and> t\<rangle>\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using lActive_greatest by fastforce
      moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<and> t\<rangle>" by simp
      ultimately show "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" by arith
    qed
    moreover have "\<forall>n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'' < (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x) \<longrightarrow> eval c t t' n'' \<gamma>'"
    proof
      fix n'' show "\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'' \<longrightarrow> n'' < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x \<longrightarrow> eval c t t' n'' \<gamma>'"
      proof (rule HOL.impI[OF HOL.impI])
        assume "\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n''" and "n'' < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x"
        show "eval c t t' n'' \<gamma>'"
        proof cases
          assume "\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
          with `n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>` have "the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
            using nAct_mono_lNact `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
          moreover have "the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>)<x"
          proof -
            from \<open>\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> have "eSuc \<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle> \<le> llength (\<pi>\<^bsub>c\<^esub>inf_llist t)"
              using nAct_llength_proj by auto
            with `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "eSuc \<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle> \<le> x" by simp
            moreover have "\<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle>\<noteq>\<infinity>" by simp
            ultimately have "Suc (the_enat(\<langle>c #\<^bsub>enat n''\<^esub>inf_llist t\<rangle>)) \<le> x"
              by (metis enat.distinct(2) the_enat.simps the_enat_eSuc the_enat_mono)
            thus ?thesis by simp
          qed
          ultimately have "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>))"
            using a1 by auto
          with `\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using validCI_act by blast      
        next
          assume "\<not>(\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
          moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'') \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
          proof -
            have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>\<le>llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using nAct_le_proj by metis
            moreover from \<open>\<not> (\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>"
              by (metis llength_eq_infty_conv_lfinite lnth_inf_llist proj_finite2)
            ultimately have "the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)\<le>the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" by simp
            moreover from \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<not> (\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> have "n''>\<langle>c \<and> t\<rangle>"
              using lActive_active by (meson leI le_eq_less_or_eq)
            hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'') > the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" using cnf2bhv_greater_llength by simp
            ultimately show ?thesis by simp
          qed
          moreover from `\<not>(\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n''" using assms(1) lActive_less by auto
            with `n'' < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'')<x" using p2c_mono_c2p_strict by simp
          ultimately have "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n''))"
            using a1 by auto
          with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using validCI_cont by blast              
        qed
      qed
    qed
    ultimately show ?thesis using `\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` by blast
  next
    assume "\<not>(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
    hence "x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" by simp
    then obtain n'::nat where "x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_exists by blast
    with \<open>enat x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close> have "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active by force
    then obtain i where "i\<ge>n'" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>" and "\<not> (\<exists>k\<ge>n'. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)" using nact_exists by blast
    moreover have "(\<forall>n''\<ge> \<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>. n''\<le>\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub> \<longrightarrow> eval c t t' n'' \<gamma>)"
    proof
      fix n'' show "\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub> \<le> n'' \<longrightarrow> n'' \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub> \<longrightarrow> eval c t t' n'' \<gamma>"
      proof(rule HOL.impI[OF HOL.impI])
        assume "\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub> \<le> n''" and "n'' \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>"
        hence "the_enat (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>) = the_enat (\<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>)"
          using nAct_same by simp
        moreover from `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>\<^esub>" using nxtActI by auto
        with `n'' \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub>` have "\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using dual_order.strict_implies_order by auto
        moreover have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>))"
        proof -
          have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
          with `x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>` `i\<ge>n'` `\<not> (\<exists>k\<ge>n'. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)` have "x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>"
            using one_enat_def nAct_not_active_same by simp
          moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
          ultimately have "x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" by fastforce        
          thus ?thesis using `\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x` by blast
        qed
        with `the_enat (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>) = the_enat (\<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>)` have
          "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>))" by simp
        ultimately show "eval c t t' n'' \<gamma>" using validCI_act by blast
      qed
    qed
    moreover have "i\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
    proof -
      have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
      with `x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>` `i\<ge>n'` `\<not> (\<exists>k\<ge>n'. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)` have "x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>"
        using one_enat_def nAct_not_active_same by simp
      moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
      ultimately have "x=the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" by fastforce        
      with `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)`
        have "the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by simp
      with `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using active_geq_nxtAct by simp
    qed
    moreover have "\<forall>n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'' < \<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub> \<longrightarrow> eval c t t' n'' \<gamma>'"
    proof
      fix n'' show "\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'' \<longrightarrow> n'' < \<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub> \<longrightarrow> eval c t t' n'' \<gamma>'"
      proof (rule HOL.impI[OF HOL.impI])
        assume "\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n''" and "n'' < \<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>"
        moreover have "\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>\<le>i" by simp
        ultimately have "\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` by (meson less_le less_le_trans)
        with `n''\<ge>\<langle>c \<leftarrow> t\<rangle>\<^bsub>n\<^esub>` have "the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
          using nAct_mono_lNact `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
        moreover have "the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) < x"
        proof -
          from `n'' < \<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>` \<open>\<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub> \<le> i\<close> have "n'' < i" using dual_order.strict_trans1 by arith
          with `n'' < \<langle>c \<leftarrow> t\<rangle>\<^bsub>i\<^esub>` have "\<exists>i'\<ge>n''. i' < i \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" using lNact_least[of i n''] by fastforce
          hence "\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>" using nAct_less by auto
          moreover have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
          with `x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>` `i\<ge>n'` `\<not> (\<exists>k\<ge>n'. k < i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)` have "x=\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>"
            using one_enat_def nAct_not_active_same by simp    
          moreover have "\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
          ultimately show ?thesis by (metis enat_ord_simps(2) enat_the_enat)
        qed
        ultimately have "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>))"
          using a1 by auto
        with `\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` show "eval c t t' n'' \<gamma>'" using validCI_act by blast
      qed
    qed
    ultimately show ?thesis using `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` by auto
  qed    
qed

lemma untilEN[elim]:
  fixes n::nat
    and n'::nat
    and t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and c::'id
  assumes "\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "eval c t t' n (\<gamma>' \<UU> \<gamma>)"
  shows "\<exists>n'\<ge>n. eval c t t' n' \<gamma> \<and>
    (\<forall>n''\<ge>n. n'' < n' \<longrightarrow> eval c t t' n'' \<gamma>')"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  moreover from `eval c t t' n (\<gamma>' \<UU> \<gamma>)`
    have "eval c t t' n (\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n'))" using until_def by simp
  ultimately have "\<exists>n''\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n). \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n'' \<and>
    (\<forall>n'\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n). n' < n'' \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n')"
    using validCE_cont[where \<gamma>="\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')"]
    `\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
  then obtain x where "x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" and "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x"
    and "\<forall>x'\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n). x'<x \<longrightarrow> \<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x'" by auto
  moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x"
  proof -
    have "\<langle>c \<and> t\<rangle> < n"
    proof (rule ccontr)
      assume "\<not>\<langle>c \<and> t\<rangle> < n"
      hence "\<langle>c \<and> t\<rangle> \<ge> n" by simp
      moreover from \<open>\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<and> t\<rangle>\<^esub>"
        using lActive_active less_or_eq_imp_le by blast
      ultimately show False using \<open>\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> by simp
    qed
    hence "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" using cnf2bhv_greater_llength by simp
    with `x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)` show ?thesis by simp
  qed
  hence "x = \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x))" using cnf2bhv_bhv2cnf by simp
  ultimately have "\<gamma> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)))" by simp
  moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  proof -
    from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using proj_finite2 by simp
    then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
    moreover from `the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x` have "\<langle>c \<and> t\<rangle> < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)"
      using bhv2cnf_greater_lActive by simp
    ultimately show ?thesis using lActive_greater_active_all by simp
  qed      
  ultimately have "eval c t t' (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)) \<gamma>" using validCI_cont `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
  moreover from `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using lActive_less[of c t _ n] by auto
  with `x\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)` have "n \<le> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)" using p2c_mono_c2p by blast
  moreover have "\<forall>n''\<ge>n. n'' < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x) \<longrightarrow> eval c t t' n'' \<gamma>'"
  proof (rule HOL.allI[OF HOL.impI[OF HOL.impI]])
    fix n'' assume "n \<le> n''" and "n'' < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)"
    hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'')\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" using cnf2bhv_mono by simp
    moreover have "n''<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x)" by (simp add: \<open>n'' < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>x\<close>)
    with \<open>\<langle>c \<and> t\<rangle> \<le> n\<close> \<open>n \<le> n''\<close> have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'')<\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x))" using cnf2bhv_mono_strict by simp
    with \<open>x = \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(x))\<close> have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'')< x" by simp
    ultimately have "\<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n''))"
      using `\<forall>x'\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n). x'<x \<longrightarrow> \<gamma>' (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t'))) x'` by simp
    moreover from `n \<le> n''` have "\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using `\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
    ultimately show "eval c t t' n'' \<gamma>'" using validCI_cont using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by blast
  qed
  ultimately show ?thesis by auto
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  moreover from `eval c t t' n (\<gamma>' \<UU> \<gamma>)`
    have "eval c t t' n (\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n'))" using until_def by simp
  ultimately have "\<exists>n''\<ge>n. \<gamma> (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n''
    \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' (lnth (\<pi>\<^bsub>c\<^esub>inf_llist t @\<^sub>l inf_llist t')) n')" using `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)`
    validCE_not_act[where \<gamma>="\<lambda> t n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')"] by blast
  with `\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using validCI_not_act by blast
qed
  
subsubsection "Weak Until"

definition wuntil :: "((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)
  \<Rightarrow> ((nat \<Rightarrow> 'cmp) \<Rightarrow> nat \<Rightarrow> bool)" (infixl "\<WW>" 20)
  where "\<gamma>' \<WW> \<gamma> \<equiv> \<gamma>' \<UU> \<gamma> \<or>\<^sup>b \<box>(\<gamma>')"

end
  
end
