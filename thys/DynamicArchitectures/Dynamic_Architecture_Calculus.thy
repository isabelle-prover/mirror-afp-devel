(*  Title:      Dynamic_Architecture_Calculus
    Author:     Diego Marmsoler
*)
section "A Calculus for Dynamic Architectures"
text {*
  The following theory formalizes our calculus of dynamic architectures~\cite{Marmsoler2017b,Marmsoler2017c} and verifies its soundness.
  The calculus allows to reason about temporal-logic specifications of component behavior in a dynamic setting.
  The theory is based on our theory of configuration traces.
*}
theory Dynamic_Architecture_Calculus
  imports Configuration_Traces

begin

subsection "Natural Numbers"
text {*
  First we provide an additional property for natural numbers.
*}
lemma boundedGreatest:
  assumes "P (i::nat)"
    and "\<forall>n' > n. \<not> P n'"
  shows "\<exists>i'\<le>n. P i' \<and> (\<forall>n'. P n' \<longrightarrow> n'\<le>i')"
proof -
  have "P (i::nat) \<Longrightarrow> n\<ge>i \<Longrightarrow> \<forall>n' > n. \<not> P n' \<Longrightarrow> (\<exists>i'\<le>n. P i' \<and> (\<forall>n'\<le>n. P n' \<longrightarrow> n'\<le>i'))"
  proof (induction n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then show ?case
    proof cases
      assume "i = Suc n"
      then show ?thesis using Suc.prems by auto
    next
      assume "\<not>(i = Suc n)"
      thus ?thesis
      proof cases
        assume "P (Suc n)"
        thus ?thesis by auto
      next
        assume "\<not> P (Suc n)"
        with Suc.prems have "\<forall>n' > n. \<not> P n'" using Suc_lessI by blast
        moreover from `\<not>(i = Suc n)` have "i \<le> n" and "P i" using Suc.prems by auto
        ultimately obtain i' where "i'\<le>n \<and> P i' \<and> (\<forall>n'\<le>n. P n' \<longrightarrow> n' \<le> i')" using Suc.IH by blast
        hence "i' \<le> n" and "P i'" and "(\<forall>n'\<le>n. P n' \<longrightarrow> n' \<le> i')" by auto
        thus ?thesis by (metis le_SucI le_Suc_eq)
      qed
    qed
  qed
  moreover have "n\<ge>i"
  proof (rule ccontr)
    assume "\<not> (n \<ge> i)"
    hence "n < i" by arith
    thus False using assms by blast
  qed
  ultimately obtain i' where "i'\<le>n" and "P i'" and "\<forall>n'\<le>n. P n' \<longrightarrow> n' \<le> i'" using assms by blast
  with assms have "\<forall>n'. P n' \<longrightarrow> n' \<le> i'" using not_le_imp_less by blast
  with `i' \<le> n` and `P i'` show ?thesis by auto
qed
  
subsection "Extended Natural Numbers"
text {*
  We also provide one additional property for extended natural numbers.
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
  
subsection "Least Not Active"
text {*
  In the following, we introduce an operator to obtain the least point in time before a certain point in time where a component was deactivated.
*}
  
definition lNAct :: "cid \<Rightarrow> CTraceINF \<Rightarrow> nat \<Rightarrow> nat" ("\<langle>_ \<or> _\<rangle>\<^bsub>_\<^esub>")
  where "\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub> \<equiv> (LEAST n'. n=n' \<or> (n'<n \<and> (\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t n'\<^esub>)))"

text {*
  Note that for the case in which there was no activation, at all, @{const lNAct} simply returns @{text n} itself.
*}
lemma lNActEx:
  fixes n
  shows "\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub> = n \<or> (\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub> < n \<and> (\<nexists>k. k\<ge>\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub> \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t (\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub>)\<^esub>))"
  by (metis (mono_tags, lifting) LeastI lNAct_def)

lemma lNactLe:
  fixes n n'
  assumes "n'=n \<or> (n'<n \<and> (\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t n'\<^esub>))"
  shows "\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub> \<le> n'"
  using lNAct_def Least_le[of "\<lambda>n'. n=n' \<or> (n'<n \<and> (\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t n'\<^esub>))"]
    using assms by auto

subsection "Last Activation"
text {*
  In the following we introduce an operator to obtain the latest point in time where a certain component was activated.
*}

definition lActive :: "cid \<Rightarrow> CTraceINF \<Rightarrow> nat" ("\<langle>_ \<and> _\<rangle>")
  where "\<langle>c \<and> t\<rangle> \<equiv> (GREATEST i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"

lemma lActive_active:
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>n' > n. \<not> (\<parallel>c\<parallel>\<^bsub>t n'\<^esub>)"
  shows "\<parallel>c\<parallel>\<^bsub>t (\<langle>c \<and> t\<rangle>)\<^esub>"
proof -
  from assms obtain i' where "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" and "(\<forall>y. \<parallel>c\<parallel>\<^bsub>t y\<^esub> \<longrightarrow> y \<le> i')"
    using boundedGreatest[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" i n] by blast
  hence "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" and "(\<forall>y. \<parallel>c\<parallel>\<^bsub>t y\<^esub> \<longrightarrow> y < (Suc i'))" by auto
  thus ?thesis using lActive_def GreatestI[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" i'] by simp
qed

lemma lActive_less:
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>n' > n. \<not> (\<parallel>c\<parallel>\<^bsub>t n'\<^esub>)"
  shows "\<langle>c \<and> t\<rangle> \<le> n"
proof (rule ccontr)
  assume "\<not> \<langle>c \<and> t\<rangle> \<le> n"
  hence "\<langle>c \<and> t\<rangle> > n" by simp
  moreover from assms have "\<parallel>c\<parallel>\<^bsub>t (\<langle>c \<and> t\<rangle>)\<^esub>" using lActive_active by simp
  ultimately show False using assms by simp
qed

lemma lActive_greatest:
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>n' > n. \<not> (\<parallel>c\<parallel>\<^bsub>t n'\<^esub>)"
  shows "i \<le> \<langle>c \<and> t\<rangle>"
proof -
  from assms obtain i' where "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" and "(\<forall>y. \<parallel>c\<parallel>\<^bsub>t y\<^esub> \<longrightarrow> y \<le> i')"
    using boundedGreatest[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" i n] by blast
  hence "(\<forall>y. \<parallel>c\<parallel>\<^bsub>t y\<^esub> \<longrightarrow> y < (Suc i'))" by auto
  with assms show ?thesis using lActive_def Greatest_le[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" i] by simp
qed
  
lemma lActive_greater_active:
  assumes "n > \<langle>c \<and> t\<rangle>"
    and "\<forall>n'' > n'. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>"
  shows "\<not> \<parallel>c\<parallel>\<^bsub>t n\<^esub>"
proof (rule ccontr)
  assume "\<not> \<not> \<parallel>c\<parallel>\<^bsub>t n\<^esub>"
  with `\<forall>n'' > n'. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>` have "n \<le> \<langle>c \<and> t\<rangle>" using lActive_greatest by simp
  thus False using assms by simp
qed
  
lemma lActive_greater_active_all:
  assumes "\<forall>n'' > n'. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>"
  shows "\<not>(\<exists>n > \<langle>c \<and> t\<rangle>. \<parallel>c\<parallel>\<^bsub>t n\<^esub>)" 
proof (rule ccontr)
  assume "\<not>\<not>(\<exists>n > \<langle>c \<and> t\<rangle>. \<parallel>c\<parallel>\<^bsub>t n\<^esub>)"
  then obtain "n" where "n>\<langle>c \<and> t\<rangle>" and "\<parallel>c\<parallel>\<^bsub>t n\<^esub>" by blast
  with `\<forall>n'' > n'. \<not> (\<parallel>c\<parallel>\<^bsub>t n''\<^esub>)` have "\<not> \<parallel>c\<parallel>\<^bsub>t n\<^esub>" using lActive_greater_active by simp
  with `\<parallel>c\<parallel>\<^bsub>t n\<^esub>` show False by simp
qed

lemma lActive_equality:
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "(\<And>x. \<parallel>c\<parallel>\<^bsub>t x\<^esub> \<Longrightarrow> x \<le> i)"
  shows "\<langle>c \<and> t\<rangle> = i" unfolding lActive_def using assms Greatest_equality[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"] by simp

subsection "Mapping Time Points"
text {*
  In the following we introduce two operators to map time-points between configuration traces and behavior traces.
*}

subsubsection "Configuration trace to behavior trace"
text {*
  First we provide an operator which maps a point in time of a configuration trace to the corresponding point in time of a behavior trace.
*}
  
definition cnf2bhv :: "cid \<Rightarrow> CTraceINF \<Rightarrow> nat \<Rightarrow> nat" ("\<^bsub>_\<^esub>\<up>\<^bsub>_\<^esub>(_)" [150,150,150] 110)
  where "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) \<equiv> the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 + (n - \<langle>c \<and> t\<rangle>)"

lemma cnf2bhv_mono:
  assumes "n'\<ge>n"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)"
  by (simp add: assms cnf2bhv_def diff_le_mono)

lemma cnf2bhv_mono_strict:
  assumes "n\<ge>\<langle>c \<and> t\<rangle>" and "n'>n"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') > \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)"
  using assms cnf2bhv_def by auto

text "Note that the functions are nat, that means that also in the case the difference is negative they will return a 0!"
lemma cnf2bhv_ge_llength[simp]:
  assumes "n\<ge>\<langle>c \<and> t\<rangle>"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) \<ge> the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  using assms cnf2bhv_def by simp

lemma cnf2bhv_greater_llength[simp]:
  assumes "n>\<langle>c \<and> t\<rangle>"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) > the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  using assms cnf2bhv_def by simp

lemma cnf2bhv_suc[simp]:
  assumes "n\<ge>\<langle>c \<and> t\<rangle>"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(Suc n) = Suc (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))"
  using assms cnf2bhv_def by simp

lemma cnf2bhv_lActive[simp]:
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<langle>c \<and> t\<rangle>) = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  using cnf2bhv_def by simp
    
lemma cnf2bhv_lnth_lappend:
  assumes act: "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and nAct: "\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) = lnth (inf_llist t') (n - \<langle>c \<and> t\<rangle> - 1)"
    (is "?lhs = ?rhs")
proof -
  from nAct have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using proj_finite2 by auto
  then obtain k where k_def: "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) = enat k" using lfinite_llength_enat by blast
  moreover have "k \<le> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)"
  proof -
    from nAct have "\<nexists>i. i>n-1 \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by simp
    with act have "\<langle>c \<and> t\<rangle> \<le> n-1" using lActive_less by auto
    moreover have "n>0" using act nAct by auto
    ultimately have "\<langle>c \<and> t\<rangle> < n" by simp
    hence "the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) - 1 < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" using cnf2bhv_greater_llength by simp
    with k_def show ?thesis by simp
  qed
  ultimately have "?lhs = lnth (inf_llist t') (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) - k)" using lnth_lappend2 by blast
  moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) - k = n - \<langle>c \<and> t\<rangle> - 1"
  proof -
    from cnf2bhv_def have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) - k = the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) - 1 + (n - \<langle>c \<and> t\<rangle>) - k"
      by simp
    also have "\<dots> = the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) - 1 + (n - \<langle>c \<and> t\<rangle>) -
      the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" using k_def by simp
    also have "\<dots> = the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) + (n - \<langle>c \<and> t\<rangle>) - 1 -
      the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
    proof -
      have "\<exists>i. enat i < llength (inf_llist t) \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) i\<^esub>" by (simp add: act)
      hence "llength (\<pi>\<^bsub>c\<^esub>inf_llist t) \<ge> 1" using proj_one by simp
      moreover from k_def have "llength (\<pi>\<^bsub>c\<^esub>inf_llist t) \<noteq> \<infinity>" by simp
      ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) \<ge> 1" by (simp add: k_def one_enat_def)
      thus ?thesis by simp
    qed
    also have "\<dots> = the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) + (n - \<langle>c \<and> t\<rangle>) -
      the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" by simp
    also have "\<dots> = n - \<langle>c \<and> t\<rangle> - 1" by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
qed    

subsubsection "Behavior trace to configuration trace"
text {*
  Next we define an operator to map a point in time of a behavior trace back to a corresponding point in time for a configuration trace.
*}

definition bhv2cnf :: "cid \<Rightarrow> CTraceINF \<Rightarrow> nat \<Rightarrow> nat" ("\<^bsub>_\<^esub>\<down>\<^bsub>_\<^esub>(_)" [150,150,150] 110)
  where "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) \<equiv> \<langle>c \<and> t\<rangle> + (n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))"

lemma bhv2cnf_mono:
  assumes "n'\<ge>n"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)"
  by (simp add: assms bhv2cnf_def diff_le_mono)    

lemma bhv2cnf_mono_strict:
  assumes "n'>n"
    and "n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') > \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)"
  using assms bhv2cnf_def by auto

text "Note that the functions are nat, that means that also in the case the difference is negative they will return a 0!"
lemma bhv2cnf_ge_lActive[simp]:
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) \<ge> \<langle>c \<and> t\<rangle>"
  using bhv2cnf_def by simp

lemma bhv2cnf_greater_lActive[simp]:
  assumes "n>the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) > \<langle>c \<and> t\<rangle>"
  using assms bhv2cnf_def by simp
    
lemma bhv2cnf_lActive[simp]:
  assumes "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) = Suc (\<langle>c \<and> t\<rangle>)"
proof -
  from assms have "\<pi>\<^bsub>c\<^esub>(inf_llist t)\<noteq> []\<^sub>l" by simp
  hence "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) > 0" by (simp add: lnull_def)
  moreover from `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) \<noteq> \<infinity>"
    using llength_eq_infty_conv_lfinite by auto
  ultimately have "the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) > 0" using enat_0_iff(1) by fastforce
  hence "the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1) = 1" by simp
  thus ?thesis using bhv2cnf_def by simp
qed
  
subsubsection "Relating the mappings"
text {*
  In the following we provide some properties about the relationship between the two mapping operators.
*}
  
lemma bhv2cnf_cnf2bhv:
  assumes "n \<ge> \<langle>c \<and> t\<rangle>"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) = n" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<langle>c \<and> t\<rangle> + ((\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))"
    using bhv2cnf_def by simp
  also have "\<dots> = \<langle>c \<and> t\<rangle> + (((the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) - 1 + (n - \<langle>c \<and> t\<rangle>)) -
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))" using cnf2bhv_def by simp
  also have "(the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) - 1 + (n - (\<langle>c \<and> t\<rangle>)) -
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1) = (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) - 1 -
    ((the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) - 1) + (n - (\<langle>c \<and> t\<rangle>))" by simp
  also have "\<dots> = n - (\<langle>c \<and> t\<rangle>)" by simp
  also have "(\<langle>c \<and> t\<rangle>) + (n - (\<langle>c \<and> t\<rangle>)) = (\<langle>c \<and> t\<rangle>) + n - \<langle>c \<and> t\<rangle>" using assms by simp
  also have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed
    
lemma cnf2bhv_bhv2cnf:
  assumes "n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)) = n" (is "?lhs = ?rhs")
proof -
  have "?lhs = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 + ((\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)) - (\<langle>c \<and> t\<rangle>))"
    using cnf2bhv_def by simp
  also have "\<dots> = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 + (\<langle>c \<and> t\<rangle> +
    (n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)) - (\<langle>c \<and> t\<rangle>))" using bhv2cnf_def by simp
  also have "\<langle>c \<and> t\<rangle> + (n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)) - (\<langle>c \<and> t\<rangle>) =
    \<langle>c \<and> t\<rangle> - (\<langle>c \<and> t\<rangle>) + (n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))" by simp
  also have "\<dots> = n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)" by simp      
  also have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 + (n - (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)) =
    n - (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1) + (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)" by simp
  also have "\<dots> = n + ((the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1) -
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))" using assms by simp
  also have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed
  
lemma p2c_mono_c2p:
  assumes "n \<ge> \<langle>c \<and> t\<rangle>"
      and "n' \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)"
    shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> n"
proof -
  from `n' \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))" using bhv2cnf_mono by simp
  thus ?thesis using bhv2cnf_cnf2bhv `n \<ge> \<langle>c \<and> t\<rangle>` by simp
qed
  
lemma c2p_mono_p2c:
  assumes "n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
      and "n' \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)"
    shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> n"
proof -
  from `n' \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n))" using cnf2bhv_mono by simp
  thus ?thesis using cnf2bhv_bhv2cnf `n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1` by simp
qed

lemma c2p_mono_p2c_strict:
  assumes "n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
      and "n<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) < n'"
proof (rule ccontr)
  assume "\<not> (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) < n')"
  hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) \<ge> n'" by simp
  with `n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(nat (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n))) \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')"
    using cnf2bhv_mono by simp
  hence "\<not>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(nat (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n))) < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'))" by simp
  with `n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1` have  "\<not>(n < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'))"
    using "cnf2bhv_bhv2cnf" by simp
  with assms show False by simp
qed
  
subsection "Behavior Trace Assertions" 
text {*
  In the following we introduce the notion of behavior trace assertions as a means to specify sets of configuration traces.
*}

text {*
  Behavior trace assertions are specified as temporal-logic formul\ae{} over atoms which are used to specify a components state.
  Satisfaction of atomic formul\ae{} is modeled in terms of a labeling function which assigns a set of component states with each atomic formula.
*}
typedecl atom
consts L :: "state \<Rightarrow> atom set"
  
datatype bhvAssert = Atom "atom"
                   | NXT bhvAssert ("\<circle>")
                   | EVT bhvAssert ("\<diamond>")
                   | GLOB bhvAssert ("\<box>")
                   | UNTIL bhvAssert bhvAssert ("_ \<uu> _")

type_synonym pos = "BTraceINF \<times> nat"
type_synonym Cpos = "CTraceINF \<times> nat"

text {*
  The semantics of behavior trace assertions for behavior traces is defined as usual~\cite{Manna2012}.
*}
primrec valid :: "pos \<Rightarrow> bhvAssert \<Rightarrow> bool" ("_ \<Turnstile> _" [80,80] 55)
  where "s \<Turnstile> Atom \<phi> = (\<phi> \<in> L ((fst s) (snd s)))" |
    "s \<Turnstile> NXT \<gamma> = ((fst s, Suc (snd s)) \<Turnstile> \<gamma>)" |
    "s \<Turnstile> EVT \<gamma> = (\<exists> n'\<ge> snd s. (fst s, n') \<Turnstile> \<gamma>)" |
    "s \<Turnstile> GLOB \<gamma> = (\<forall> n'\<ge> snd s. (fst s, n') \<Turnstile> \<gamma>)" |
    "s \<Turnstile> UNTIL \<gamma>' \<gamma> = (\<exists>n''\<ge>snd s. (fst s, n'') \<Turnstile> \<gamma> \<and> (\<forall>n'\<ge>snd s. n'<n'' \<longrightarrow> (fst s, n') \<Turnstile> \<gamma>'))"

text {*
  However, we provide an alternative interpretation over configuration traces to interpret temporal specifications of component behavior in a dynamic context.
*}
definition validC :: "Cpos \<Rightarrow> BTraceINF \<Rightarrow> cid \<Rightarrow> bhvAssert \<Rightarrow> bool" ("_ \<Turnstile>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _" [50,50,50,50] 80)
  where "s \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma> \<equiv>
    ((\<exists>i\<ge>(snd s). \<parallel>c\<parallel>\<^bsub>fst s i\<^esub>) \<and>
      ((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst s))) @\<^sub>l (inf_llist t')), the_enat(\<langle>c #\<^bsub>snd s\<^esub> inf_llist (fst s)\<rangle>)) \<Turnstile> \<gamma>)) \<or>
    ((\<exists>i. \<parallel>c\<parallel>\<^bsub>fst s i\<^esub>) \<and> ((\<nexists>i'. i'\<ge>(snd s) \<and> \<parallel>c\<parallel>\<^bsub>fst s i'\<^esub>)) \<and>
      ((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst s))) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>fst s\<^esub>(snd s)) \<Turnstile> \<gamma>)) \<or>
    ((\<nexists>i. \<parallel>c\<parallel>\<^bsub>fst s i\<^esub>) \<and> ((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst s))) @\<^sub>l (inf_llist t')), snd s) \<Turnstile> \<gamma>))"

lemma validCI_act[simp]:
  assumes "\<exists>i\<ge>(snd s). \<parallel>c\<parallel>\<^bsub>fst s i\<^esub>"
    and "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst s))) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>snd s\<^esub> inf_llist (fst s)\<rangle>)) \<Turnstile> \<gamma>"
  shows "s \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
  using assms validC_def by simp

lemma validCI_cont[simp]:
  assumes "\<exists>i. \<parallel>c\<parallel>\<^bsub>fst s i\<^esub>"
    and "(\<nexists>i'. i'\<ge>(snd s) \<and> \<parallel>c\<parallel>\<^bsub>fst s i'\<^esub>)"
    and "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst s))) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>fst s\<^esub>(snd s)) \<Turnstile> \<gamma>"
  shows "s \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
  using assms validC_def by simp

lemma validCI_not_act[simp]:
  assumes "\<nexists>i. \<parallel>c\<parallel>\<^bsub>fst s i\<^esub>"
    and "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst s))) @\<^sub>l (inf_llist t')), snd s) \<Turnstile> \<gamma>"
  shows "s \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
  using assms validC_def by simp

lemma validCE_act[simp]:
  assumes "\<exists>i\<ge>(snd s). \<parallel>c\<parallel>\<^bsub>fst s i\<^esub>"
  shows "s \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma> \<Longrightarrow>
    (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst s))) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>snd s\<^esub> inf_llist (fst s)\<rangle>)) \<Turnstile> \<gamma>"
  using assms validC_def by blast
    
lemma validCE_cont[simp]:
  assumes "\<exists>i. \<parallel>c\<parallel>\<^bsub>fst s i\<^esub>"
    and "\<nexists>i'. i'\<ge>(snd s) \<and> \<parallel>c\<parallel>\<^bsub>fst s i'\<^esub>"
  shows "s \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma> \<Longrightarrow> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst s))) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>fst s\<^esub>(snd s)) \<Turnstile> \<gamma>"
  using assms validC_def by blast

lemma validCE_not_act[simp]:
  assumes "\<nexists>i. \<parallel>c\<parallel>\<^bsub>fst s i\<^esub>"
  shows "s \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma> \<Longrightarrow> ((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst s))) @\<^sub>l (inf_llist t')), snd s) \<Turnstile> \<gamma>)"
  using assms validC_def by blast

lemma validity1:
  assumes "n\<le>n'"
    and "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>k\<ge>n. k<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
  shows "(t,n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma> \<Longrightarrow> (t,n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
proof -
  assume "(t,n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
  moreover from assms have "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by (meson order.trans)
  ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>"
    using validCE_act[of "(t, n)" c t' \<gamma>] by simp      
  moreover have "enat n' - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
  with assms have "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>) = the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)"
    using nAct_not_active_same[of n n' "inf_llist t" c] by simp
  ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>"
    by simp     
  with assms show "(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" using validCI_act[of "(t, n')" c t' \<gamma>] by simp
qed
  
lemma validity2:
  assumes "n\<le>n'"
    and "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>k\<ge>n. k<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
  shows "(t,n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma> \<Longrightarrow> (t,n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
proof -
  assume "(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma> "
  with `\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
    have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>"
    using validCE_act[of "(t, n')" c t' \<gamma>] by simp
  moreover have "enat n' - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
  with assms have "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>) = the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)"
    using nAct_not_active_same by simp
  ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>"
    by simp     
  moreover from assms have "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by (meson order.trans)      
  ultimately show "(t,n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" using validCI_act[of "(t, n)" c t' \<gamma>] by simp
qed
  
subsection "Verifying the Calculus"
text {*
  We are now able to formalize all the rules of the calculus presented in~\cite{Marmsoler2017c}.
*}

subsubsection "Atomic Assertions"
  
lemma bAssIA:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<And>i. \<lbrakk>i\<ge>n; \<parallel>c\<parallel>\<^bsub>t i\<^esub>;  \<not>(\<exists>k\<ge>n. k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)\<rbrakk> \<Longrightarrow> \<phi> \<in> L (state (tCMP c (t i)))"
  shows "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> Atom \<phi>"
proof -
  from \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> obtain i where "i\<ge>n" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>" and "\<nexists>k. n\<le>k \<and> k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
    using lActive_least[of n "inf_llist t" c] by auto
  with assms have "\<phi> \<in> L (state (tCMP c (t i)))" by simp
  moreover have "lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)) = state (tCMP c (t i))"
  proof -
    have "enat (Suc i) < llength (inf_llist t)" using enat_ord_code by simp
    moreover from `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) i\<^esub>" by simp
    ultimately show ?thesis using proj_active_nth by simp
  qed
  ultimately have "\<phi> \<in> L (lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)))" by simp
  moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>"
  proof -
    from `\<nexists>k. n\<le>k \<and> k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>` have "\<not> (\<exists>k\<ge>n. k < i \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) k\<^esub>)" by simp
    moreover have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
    ultimately show ?thesis using `i\<ge>n` nAct_not_active_same[of n i "inf_llist t" c] by simp
  qed
  ultimately have "\<phi> \<in> L (lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))" by simp
  moreover have "enat (the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)) < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
  proof -
    have "ltake \<infinity> (inf_llist t) = (inf_llist t)" using ltake_all[of "inf_llist t"] by simp
    hence "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) = \<langle>c #\<^bsub>\<infinity>\<^esub> inf_llist t\<rangle>" using nAct_def by simp
    moreover have "\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>\<infinity>\<^esub> inf_llist t\<rangle>"
    proof -
      have "enat i < llength (inf_llist t)" by simp
      with `i\<ge>n` `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using nAct_less[of i "inf_llist t" n \<infinity>] by simp
    qed
    ultimately show ?thesis by simp
  qed
  hence "lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) =
    lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
    using lnth_lappend1[of "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)" "\<pi>\<^bsub>c\<^esub>(inf_llist t)" "inf_llist t'"] by simp
  ultimately have "\<phi> \<in> L (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))" by simp
  hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> Atom \<phi>" by simp
  with \<open>i\<ge>n\<close> \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> have "(\<exists>i\<ge>snd (t, n). \<parallel>c\<parallel>\<^bsub>fst (t, n) i\<^esub>) \<and>
    (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist (fst (t, n)))) @\<^sub>l (inf_llist t')),
    the_enat (\<langle>c #\<^bsub>the_enat (snd (t,n))\<^esub> inf_llist (fst (t, n))\<rangle>)) \<Turnstile> Atom \<phi>" by auto
  thus ?thesis by simp
qed

lemma bAssIN1:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat  
  assumes act: "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and nAct: "\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and al: "\<phi> \<in> L (t' (n - \<langle>c \<and> t\<rangle> - 1))"
  shows "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> Atom \<phi>"
proof -
  have "t' (n - \<langle>c \<and> t\<rangle> - 1) = lnth (inf_llist t') (n - \<langle>c \<and> t\<rangle> - 1)" by simp
  moreover have "\<dots> = lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))"
    using act nAct cnf2bhv_lnth_lappend by simp
  ultimately have "\<phi> \<in> L (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)))" using al by simp
  hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))) \<Turnstile> Atom \<phi>" by simp
  with act nAct show ?thesis by simp
qed    
    
lemma bAssIN2:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat  
  assumes nAct: "\<nexists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and al: "\<phi> \<in> L (t' n)"
  shows "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> Atom \<phi>"
proof -
  have "t' n = lnth (inf_llist t') n" by simp
  moreover have "\<dots> = lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n"
  proof -
    from nAct have "\<pi>\<^bsub>c\<^esub>(inf_llist t) = []\<^sub>l" by simp
    hence "(\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t') = inf_llist t'" by (simp add: \<open>\<pi>\<^bsub>c\<^esub>inf_llist t = []\<^sub>l\<close>)
    thus ?thesis by simp
  qed
  ultimately have "\<phi> \<in> L (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n)" using al by simp
  hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), n) \<Turnstile> Atom \<phi>" by simp
  with nAct show ?thesis by simp
qed

lemma bAssEA:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat
    and i::nat    
  assumes sat: "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> Atom \<phi>"
    and "n\<le>i"
    and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<not>(\<exists>k\<ge>n. k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
  shows "\<phi> \<in> L (state (tCMP c (t i)))"
proof -
  from sat have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> Atom \<phi>"
    using `n\<le>i` `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` validCE_act[of "(t,n)" c t' "Atom \<phi>"] by auto
  hence "\<phi> \<in> L (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))" by simp
  moreover have "enat (the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)) < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
  proof -
    have "ltake \<infinity> (inf_llist t) = (inf_llist t)" using ltake_all[of "inf_llist t"] by simp
    hence "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) = \<langle>c #\<^bsub>\<infinity>\<^esub> inf_llist t\<rangle>" using nAct_def by simp
    moreover have "\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>\<infinity>\<^esub> inf_llist t\<rangle>"
    proof -
      have "enat i < llength (inf_llist t)" by simp
      with `i\<ge>n` `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using nAct_less[of i "inf_llist t" n \<infinity>] by simp
    qed
    ultimately show ?thesis by simp
  qed
  hence "lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) =
    lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
    using lnth_lappend1[of "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)" "\<pi>\<^bsub>c\<^esub>(inf_llist t)" "inf_llist t'"] by simp
  ultimately have "\<phi> \<in> L (lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)))" by simp
  moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>"
  proof -
    from `\<nexists>k. n\<le>k \<and> k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>` have "\<not> (\<exists>k\<ge>n. k < i \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) k\<^esub>)" by simp
    moreover have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
    ultimately show ?thesis using `i\<ge>n` nAct_not_active_same[of n i "inf_llist t" c] by simp
  qed      
  moreover have "lnth (\<pi>\<^bsub>c\<^esub>(inf_llist t)) (the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)) = state (tCMP c (t i))"
  proof -
    have "enat (Suc i) < llength (inf_llist t)" using enat_ord_code by simp
    moreover from `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) i\<^esub>" by simp
    ultimately show ?thesis using proj_active_nth by simp
  qed
  ultimately show ?thesis by simp
qed
    
lemma bAssEN1:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat  
  assumes act: "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and nAct: "\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and al: "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> Atom \<phi>"
  shows "\<phi> \<in> L (t' (n - \<langle>c \<and> t\<rangle> - 1))"
proof -
  from al have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))) \<Turnstile> Atom \<phi>"
    using act nAct validCE_cont[of c "(t,n)" t' "Atom \<phi>"] by auto
  hence "\<phi> \<in> L (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)))" by simp
  moreover have "lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) = lnth (inf_llist t') (n - \<langle>c \<and> t\<rangle> - 1)"
    using act nAct cnf2bhv_lnth_lappend by simp
  moreover have "\<dots> = t' (n - \<langle>c \<and> t\<rangle> - 1)" by simp
  ultimately show ?thesis by simp
qed

lemma bAssEN2:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat  
  assumes nAct: "\<nexists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and al: "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> Atom \<phi>"
  shows "\<phi> \<in> L (t' n)"
proof -
  from al have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), n) \<Turnstile> Atom \<phi>"
    using nAct validCE_not_act[of c "(t,n)" t' "Atom \<phi>"] by auto
  hence "\<phi> \<in> L (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n)" by simp
  moreover have "lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) n = lnth (inf_llist t') n"
  proof -
    from nAct have "\<pi>\<^bsub>c\<^esub>(inf_llist t) = []\<^sub>l" by simp
    hence "(\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t') = inf_llist t'" by (simp add: \<open>\<pi>\<^bsub>c\<^esub>inf_llist t = []\<^sub>l\<close>)
    thus ?thesis by simp
  qed
  moreover have "\<dots> = t' n" by simp
  ultimately show ?thesis by simp
qed    

subsubsection "Next Operator"

lemma bNxtIA:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
      and "\<And>i n. \<lbrakk>i\<ge>n; \<parallel>c\<parallel>\<^bsub>t i\<^esub>;  \<not>(\<exists>k\<ge>n. k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)\<rbrakk> \<Longrightarrow> (t, Suc i) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
  shows "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<circle>\<gamma>"
proof -
  from \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> obtain i where "i\<ge>n" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>" and "\<nexists>k. n\<le>k \<and> k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
    using lActive_least[of n "inf_llist t" c] by auto
  with assms have "(t, Suc i) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" by simp
  show ?thesis
  proof cases
    assume "\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
    hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat(\<langle>c #\<^bsub>Suc i\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>"
    proof
      fix i' assume "i<i' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
      hence "i' \<ge> Suc i" by simp
      with `i<i' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>` have "\<exists>i'\<ge>Suc i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by blast
      with `(t, Suc i) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>`
        show "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>enat (Suc i)\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>"
        using validCE_act[of "(t, Suc i)"] by simp
    qed
    moreover have "the_enat(\<langle>c #\<^bsub>Suc i\<^esub> inf_llist t\<rangle>) = Suc(the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>))"
    proof -
      have "i < llength (inf_llist t)" by simp
      moreover from `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) i\<^esub>" by simp
      ultimately have "the_enat(\<langle>c #\<^bsub>Suc i\<^esub> inf_llist t\<rangle>) = the_enat(eSuc (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>))" by simp
      moreover have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
      ultimately show ?thesis using the_enat_eSuc by simp
    qed
    ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), Suc (the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>))) \<Turnstile> \<gamma>"
      by simp
    hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<circle> \<gamma>" by simp
    moreover have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
    with `\<nexists>k. n\<le>k \<and> k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>` `i\<ge>n` have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
      using nAct_not_active_same by simp
    ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<circle> \<gamma>"
      by simp
    with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis by simp
  next
    assume "\<not> (\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
    hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(Suc i)) \<Turnstile> \<gamma>"
    proof -
      assume "\<not> (\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
      hence "\<not> (\<exists>i'\<ge>Suc i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)" by simp
      moreover from \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> have "\<exists>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by auto
      ultimately show ?thesis using `(t, Suc i) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>` validCE_cont[of c "(t, Suc i)" t'] by simp
    qed
    moreover from `\<not> (\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` and \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> have "i=\<langle>c \<and> t\<rangle>" using lActive_equality leI by blast
    ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), Suc (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(i))) \<Turnstile> \<gamma>"
      using cnf2bhv_suc by simp
    hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(i)) \<Turnstile> \<circle> \<gamma>" by simp
    moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(i) = the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
    proof -
      from `i=\<langle>c \<and> t\<rangle>` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(i) = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" by simp
      also have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) = eSuc (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)"
      proof -
        from `\<not> (\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "\<not> (\<exists>i'\<ge> Suc i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)" by simp
        hence "\<langle>c #\<^bsub>Suc i\<^esub> inf_llist t\<rangle> = llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
          using nAct_eq_proj[of "Suc i" c "inf_llist t"] by simp
        moreover from \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> have "\<langle>c #\<^bsub>Suc i\<^esub> inf_llist t\<rangle> = eSuc (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)" by simp
        ultimately show ?thesis by simp
      qed
      also have "the_enat(eSuc (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)) - 1 = (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)"
      proof -
        have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
        hence "the_enat(eSuc (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)) = Suc(the_enat(\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>))"
          using the_enat_eSuc by simp
        thus ?thesis by simp
      qed
      also have "\<dots> = the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
      proof -
        have "enat i - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
        with `\<nexists>k. n\<le>k \<and> k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>` and `i\<ge>n` show ?thesis
          using nAct_not_active_same[of n i] by simp
      qed
      finally show ?thesis by blast
    qed
    ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<circle> \<gamma>"
      by simp
    with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using validCI_act[of "(t, n)" c t' "\<circle> \<gamma>"] by simp
  qed
qed
  
lemma bNxtEA:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat
    and "i"
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<circle>\<gamma>"
    and "i\<ge>n"
    and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<not>(\<exists>k\<ge>n. k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
  shows "(t, Suc i) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
proof -
  from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` and `(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<circle> \<gamma>`
    have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<circle> \<gamma>"
    using validCE_act[of "(t,n)" c t' "\<circle> \<gamma>"] by simp
  moreover from assms have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
    using nAct_not_active_same[of n i "inf_llist t" c] by (simp add: one_enat_def)
  ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<circle> \<gamma>"
    by simp
  hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), Suc (the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>))) \<Turnstile> \<gamma>" by simp
  show ?thesis
  proof cases
    assume "\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
    hence "\<exists>i'\<ge>Suc i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" using Suc_leI by blast
    hence "\<exists>i'\<ge>Suc i. i' < llength (inf_llist t) \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) i'\<^esub> \<and>
      \<not> (\<exists>k\<ge>Suc i. k < i' \<and> enat k < llength (inf_llist t) \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) k\<^esub>)"
      using lActive_least[of "Suc i" "inf_llist t" c] by simp
    then obtain i' where "i'\<ge>Suc i" and "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" and
      "\<not> (\<exists>k\<ge>Suc i. k < i' \<and> enat k < llength (inf_llist t) \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) k\<^esub>)" by auto
    hence "i<i'" and "\<forall>k>i. k < i' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>" by auto
    hence "\<langle>c #\<^bsub>enat i'\<^esub> inf_llist t\<rangle> = eSuc (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>)"
      using nAct_active_suc[of "inf_llist t" i' i i c] le_neq_trans `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` by auto
    hence "the_enat (\<langle>c #\<^bsub>i'\<^esub> inf_llist t\<rangle>)=Suc (the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>))" by (simp add: the_enat_eSuc)
    with `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), Suc (the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>))) \<Turnstile> \<gamma>`
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>i'\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>" by simp
    moreover from `\<parallel>c\<parallel>\<^bsub>t i'\<^esub>` have "\<exists>i\<ge>i'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by blast
    ultimately have "(t, i') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" using validCI_act[of "(t,i')" c t' \<gamma>] by simp
    with \<open>\<exists>i\<ge>i'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<forall>k>i. k < i' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>\<close> \<open>i < i'\<close> show ?thesis
      using Suc_le_eq validity2 by auto
  next
    assume "\<not>(\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
    with `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "i=\<langle>c \<and> t\<rangle>" using lActive_equality not_le_imp_less by blast
    hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(i) = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" by simp
    moreover have "the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>) = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) -1"
    proof -
      from `\<not>(\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "\<not>(\<exists>i'\<ge> Suc i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)" by simp
      hence "\<langle>c #\<^bsub>enat (Suc i)\<^esub> inf_llist t\<rangle> = llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using nAct_eq_proj[of "Suc i" c "inf_llist t"] by simp
      moreover from `\<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<langle>c #\<^bsub>enat (Suc i)\<^esub> inf_llist t\<rangle> = eSuc (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>)" by simp
      ultimately have "eSuc (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>) = llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" by simp
      moreover have "\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
      ultimately have "Suc (the_enat (\<langle>c #\<^bsub>enat i\<^esub> inf_llist t\<rangle>)) = llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using eSuc_enat by fastforce
      thus ?thesis by (metis diff_Suc_1 the_enat.simps)
    qed
    ultimately have "the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>) = \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(i)" by simp
    hence "Suc (the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)) = Suc (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(i))" by simp
    moreover from \<open>\<not> (\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)\<close> have "i\<ge>\<langle>c \<and> t\<rangle>" using assms(4) lActive_less by blast
    ultimately have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(Suc i) = Suc (the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>))"
      using cnf2bhv_suc[of c t i] by simp
    with `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), Suc (the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>))) \<Turnstile> \<gamma>`
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(Suc i)) \<Turnstile> \<gamma>" by simp
    moreover from `\<not>(\<exists>i'>i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "\<not>(\<exists>i'\<ge>Suc i. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)" by simp
    ultimately show ?thesis using `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validCI_cont[of c "(t,Suc i)" t' \<gamma>] by fastforce
  qed
qed
  
lemma bNxtIN:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat  
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "(t, Suc n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
  shows "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<circle> \<gamma>"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  with assms have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(Suc n)) \<Turnstile> \<gamma>"
    using validCE_cont[of c "(t,Suc n)"] by simp
  with \<open>\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), Suc (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))) \<Turnstile> \<gamma>"
    using `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` lActive_less by auto
  hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<Turnstile> \<circle> \<gamma>" using valid.simps by simp
  with `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using validCI_cont[of c "(t,Suc n)"] by simp
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms show ?thesis using validC_def by auto
qed

lemma bNxtEN:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat 
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<circle>\<gamma>"
  shows "(t, Suc n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  with assms have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<Turnstile> \<circle> \<gamma>"
    using validCE_cont[of c "(t,n)" t' "\<circle> \<gamma>"] by simp
  with \<open>\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<Turnstile> \<circle> \<gamma>" by auto
  hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), Suc (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))) \<Turnstile> \<gamma>" by simp
  hence "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(Suc n)) \<Turnstile> \<gamma>"
    using \<open>\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> assms(1) lActive_less by auto
  with `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` show ?thesis using validCI_cont[of c "(t,Suc n)"] by simp
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms show ?thesis using validC_def by auto
qed

subsubsection "Eventually Operator"  

lemma bEvtI:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat
    and n'::nat
  assumes "n'\<ge>n"
    and "(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
  shows "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<diamond>\<gamma>"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"    
  show ?thesis
  proof cases
    assume "\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
    with `(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>`
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>"
      using validCE_act[of "(t,n')" c t' \<gamma>] by simp
    moreover have "the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>) \<le> the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)"
    proof -
      from `n\<le>n'` have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_mono by simp
      moreover have "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
      ultimately show ?thesis by simp
    qed
    ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<diamond> \<gamma>"
      by auto
    moreover have "\<exists>i'\<ge>n. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
    proof -
      from `\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>` obtain i' where "i'\<ge>n'" and "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by blast
      with `n'\<ge>n` have "i'\<ge> n" by simp
      with `\<parallel>c\<parallel>\<^bsub>t i'\<^esub>` show ?thesis by blast
    qed
    ultimately show ?thesis by simp
  next
    assume "\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
    with `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>` have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')) \<Turnstile> \<gamma>"
      using validCE_cont[of c "(t, n')"] by simp
    then show ?thesis
    proof cases
      assume "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
      moreover have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<diamond> \<gamma>"
      proof -
        have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
        proof -
          from `\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "n' \<ge> \<langle>c \<and> t\<rangle>" using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` lActive_less by auto
          hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" using cnf2bhv_ge_llength by simp
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
        with `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')) \<Turnstile> \<gamma>` show ?thesis by auto
      qed
      ultimately show ?thesis by simp
    next
      assume "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
      moreover from `n'\<ge>n` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" using cnf2bhv_mono by simp
      with `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')) \<Turnstile> \<gamma>`
        have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<Turnstile> \<diamond> \<gamma>" by auto
      ultimately show ?thesis using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
    qed
  qed
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms show ?thesis using validC_def by auto
qed
  
lemma bEvtEA:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat  
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<diamond>\<gamma>"
  shows "\<exists>n'\<ge>\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub>. (t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
proof -
  from assms have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<diamond>\<gamma>"
    using validCE_act[of "(t,n)" c t' "\<diamond>\<gamma>"] by simp
  then obtain x where "x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" and
    "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>" by auto
  thus ?thesis
  proof (cases)
    assume "(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
    moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>"
      by (metis infinity_ileE)
    moreover from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<ge>1"
      using proj_one[of "inf_llist t"] by auto
    ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x"
      by (metis One_nat_def Suc_ile_eq antisym_conv2 diff_Suc_less enat_ord_simps(2)
          enat_the_enat less_imp_diff_less one_enat_def) (*Refactor*)
    hence "x = \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" using cnf2bhv_bhv2cnf by simp
    with `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>`
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))) \<Turnstile> \<gamma>" by simp
    moreover have "\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    proof -
      from `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
      then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
      moreover from `the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x` have "\<langle>c \<and> t\<rangle> < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)"
        using bhv2cnf_greater_lActive by simp
      ultimately show ?thesis using lActive_greater_active_all by simp
    qed
    ultimately have "(t, \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
      using `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validCI_cont[of c "(t,\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))"] by fastforce
    moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<or> t\<rangle>\<^bsub>n\<^esub>"
    proof -
      from `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
      then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
      with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<langle>c \<and> t\<rangle>\<ge>n" using lActive_greatest by fastforce
      moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<and> t\<rangle>" by simp
      ultimately have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> n" by arith
      thus ?thesis using lNactLe by (metis HOL.no_atp(11))
    qed
    ultimately show ?thesis by blast
  next
    assume "\<not>(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
    hence "x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" by simp
    then obtain n'::nat where "x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_exists by blast
    moreover have "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
    ultimately have "x=the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)" by fastforce
    with `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>`
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>" by simp
    moreover from \<open>enat x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close> \<open>enat x = \<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>\<close>
      have "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active by force
    ultimately have "(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" using validCI_act by simp
    moreover have "n'\<ge>\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub>"
    proof cases
      assume "n'\<ge>n"
      thus ?thesis using lNactLe by (metis HOL.no_atp(11))
    next
      assume "\<not>n'\<ge>n"
      hence "n'<n" by simp
      with `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)` have "x=the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
        by (simp add: \<open>x = the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)\<close> dual_order.antisym nAct_mono)
      with `x=the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)`
        have "the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)=the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)" by simp
      hence "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" by (metis enat.distinct(2) nAct_enat_the_nat)
      with `n'<n` have "\<not> \<parallel>c\<parallel>\<^bsub>t n'\<^esub>" using nAct_same_not_active[of c n t n'] by simp
      with `n'<n` show ?thesis using lNactLe by auto
    qed
    ultimately show ?thesis by blast
  qed    
qed
  
lemma bEvtEN:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat
    and n'::nat  
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    and "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<diamond>\<gamma>"
  shows "\<exists>n'\<ge>n. (t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" 
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  with `(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<diamond> \<gamma>` have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<Turnstile> \<diamond>\<gamma>"
    using validCE_cont[of c "(t,n)" t' "\<diamond>\<gamma>"] `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` by simp
  then obtain x where "x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" and "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>" by auto
  moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x"
  proof -
    from `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using lActive_less[of c t _ n] by auto
    hence "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 \<le> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" using cnf2bhv_ge_llength by simp
    with \<open>\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> `x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)` show ?thesis
      by (metis cnf2bhv_greater_llength lActive_active leD not_le_imp_less
          order.strict_implies_order order.trans) (*refactor*)
  qed
  hence "x = \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" using cnf2bhv_bhv2cnf by simp
  ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))) \<Turnstile> \<gamma>" by simp
  moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  proof -
    from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using proj_finite2 by simp
    then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
    moreover from `the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x` have "\<langle>c \<and> t\<rangle> < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)"
      using bhv2cnf_greater_lActive by simp
    ultimately show ?thesis using lActive_greater_active_all by simp
  qed      
  ultimately have "(t, \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
    using validCI_cont[of c "(t, \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" t' \<gamma>] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
  moreover from `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using lActive_less[of c t _ n] by auto
  with `x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)` have "n \<le> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)" using p2c_mono_c2p by blast  
  ultimately show ?thesis by auto
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms show ?thesis using validC_def by auto
qed    

subsubsection "Globally Operator"
  
lemma bGlobI:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat  
  assumes "\<And>n'. n'\<ge>n \<Longrightarrow> (t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
  shows "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<box>\<gamma>"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"    
  show ?thesis    
  proof cases
    assume "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    moreover have "((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<box> \<gamma>)"
    proof -
      have "\<forall>x::nat\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>). ((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>)"
      proof
        fix x::nat show
          "(x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<longrightarrow> ((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>)"
        proof
          assume "x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
          show "((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>)"
          proof (cases)
            assume "(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
            hence "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
              using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
            then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
            
            with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<langle>c \<and> t\<rangle>\<ge>n" using lActive_greatest by fastforce
            moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<and> t\<rangle>" by simp
            ultimately have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> n" by arith
            with assms have "(t, \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" by simp    
            
            moreover have "\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
            proof -
              from `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
                have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) = Suc (\<langle>c \<and> t\<rangle>)"
                using bhv2cnf_lActive by blast
              moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))` have "x \<ge> the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
                using the_enat_mono by fastforce
              hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))))"
                using bhv2cnf_mono[of "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" x] by simp
              ultimately have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> Suc (\<langle>c \<and> t\<rangle>)" by simp
              hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) > \<langle>c \<and> t\<rangle>" by simp
              with `\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>` show ?thesis using lActive_greater_active_all by simp
            qed
            ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))) \<Turnstile> \<gamma>"
              using validCE_cont[of c "(t,\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" t' \<gamma>] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
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
            hence "\<exists>(n'::nat). x = \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_exists by simp
            then obtain n'::nat where "x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" by blast
  
            have "(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
            proof cases
              assume "x=the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
              with `x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>` have "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
                and "x = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" by auto
              show ?thesis
              proof cases
                assume "n\<ge>n'"
                with `\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>` have "\<forall>k\<ge>n'. k<n \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
                  using nAct_same_not_active[of c "(enat n)" t "enat n'"] by simp
                moreover from assms have "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" by simp
                ultimately show ?thesis using `n\<ge>n'` `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validity2[of n' n c t t' \<gamma>] by simp
              next
                assume "\<not>n\<ge>n'"
                hence "n\<le>n'" by simp                
                with `\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>` have "\<forall>k\<ge>n. k<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
                  using nAct_same_not_active[of c "(enat n')" t "enat n"] by simp                
                moreover from `x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>` `x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))`
                  have "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active[of x c "inf_llist t" n'] by simp                  
                moreover from assms have "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" by simp
                ultimately show ?thesis using `n'\<ge>n` validity1[of n n' c t t' \<gamma>] by simp
              qed
            next
              assume "\<not>(x=the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
              with `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)` have "x > the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by simp
              moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
              ultimately have "x > \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" by fastforce
              with `x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>` have "enat n'\<ge>enat n"
                using nAct_mono_back[of c "(enat n)" "(inf_llist t)" "enat n'"] by simp
              with assms show ?thesis by simp
            qed
            moreover from `x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>` `x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))`
              have "\<exists>i. n' \<le> enat i \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active[of x c "inf_llist t" n'] by simp
            ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>"
                using validCE_act[of "(t,n')" c t' \<gamma>] by simp
            with `x = \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>`
              have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat x) \<Turnstile> \<gamma>" by simp
            thus ?thesis by simp
          qed
        qed
      qed
      thus ?thesis by simp
    qed
    ultimately show ?thesis using validCI_act by simp
  next
    assume "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    hence "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using proj_finite2 by simp
    then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
    
    have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<Turnstile> \<box> \<gamma>"
    proof -
      have "\<forall>x::nat\<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n). ((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>)"
      proof
        fix x::nat show "(x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<longrightarrow> ((lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>)"
        proof
          assume "x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)"
          moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` lActive_less by auto
          ultimately have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> n" using p2c_mono_c2p by simp
          with assms have "(t, \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" by simp    
          moreover have "\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
          proof -
            from `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
              have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) = Suc (\<langle>c \<and> t\<rangle>)"
              using bhv2cnf_lActive by blast
            moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "n>\<langle>c \<and> t\<rangle>"
              by (meson `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` lActive_active leI le_eq_less_or_eq)
            hence "n\<ge>Suc (\<langle>c \<and> t\<rangle>)" by simp
            with `x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> n" using p2c_mono_c2p by simp
            with `n\<ge>Suc(\<langle>c \<and> t\<rangle>)` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> Suc (\<langle>c \<and> t\<rangle>)" by simp
            hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) > \<langle>c \<and> t\<rangle>" by simp
            with `\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>` show ?thesis using lActive_greater_active_all by simp
          qed
          ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))) \<Turnstile> \<gamma>"
            using validCE_cont[of c "(t,\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" t' \<gamma>] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
          moreover have "x \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
            using \<open>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) \<le> x\<close> cnf2bhv_def by auto
          ultimately show "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>"
            using cnf2bhv_bhv2cnf by simp
        qed
      qed
      thus ?thesis by simp
    qed
    with `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` show ?thesis using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validCI_cont[of c "(t,n)"] by simp
  qed
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms show ?thesis using validC_def by auto
qed
  
lemma bGlobE:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat
    and n'::nat
  assumes "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<box>\<gamma>"
    and "n'\<ge>n"
  shows "(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
proof cases
  assume "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  with `(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<box>\<gamma>`
    have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<box>\<gamma>"
    using validCE_act[of "(t,n)" c t' "\<box>\<gamma>"] by simp
  hence "\<forall>x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>).(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>" by simp      
  show ?thesis
  proof cases
    assume "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    moreover from `n'\<ge>n` have "the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>) \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
      using nAct_mono by simp
    with `\<forall>x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>).(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>`
    have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>" by simp
    ultimately show ?thesis using validCI_act[of "(t, n')" c t'] by simp
  next
    assume "\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
    proof -
      have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>\<le>llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using nAct_le_proj by metis
      moreover from \<open>\<not> (\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>"
        by (metis llength_eq_infty_conv_lfinite lnth_inf_llist proj_finite2)
      ultimately have "the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)\<le>the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" by simp
      moreover from \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<not> (\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> have "n'>\<langle>c \<and> t\<rangle>"
        using lActive_active by (meson leI le_eq_less_or_eq)
      hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') > the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" using cnf2bhv_greater_llength by simp
      ultimately show ?thesis by simp
    qed
    with `\<forall>x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>).(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>`
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')) \<Turnstile> \<gamma>" by simp
    ultimately show ?thesis using validCI_cont[of c "(t, n')" t' \<gamma>] `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by fastforce
  qed
next
  assume "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  show ?thesis
  proof cases
    assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    with `(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<box>\<gamma>` have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<Turnstile> \<box>\<gamma>"
      using validCE_cont[of c "(t,n)" t' "\<box>\<gamma>"] `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` by simp
    hence "\<forall>x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n). (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>" by simp
    moreover from `n'\<ge>n` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" using cnf2bhv_mono by simp
    ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')) \<Turnstile> \<gamma>" by simp
    moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` `n'\<ge>n` have "\<not>(\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)" by simp
    ultimately show ?thesis using validCI_not_act[of c "(t, n')" t' \<gamma>] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
  next
    assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    with assms show ?thesis using validC_def by auto
  qed
qed

subsubsection "Until Operator"
  
lemma bUntilI:
  fixes c::cid
    and t::CTraceINF
    and t'::BTraceINF
    and n::nat
    and n'::nat
  assumes "n'\<ge>n"
    and "(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>"
    and a1: "\<And>n'' i''. \<lbrakk>n\<le>n''; n''\<le>i''; \<parallel>c\<parallel>\<^bsub>t i''\<^esub>; i''<n'\<rbrakk> \<Longrightarrow> (t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'"
    and a2: "\<And>n''. \<lbrakk>n\<le>n''; n''<n'; \<nexists>i''. i''\<ge>n'' \<and>  \<parallel>c\<parallel>\<^bsub>t i''\<^esub>\<rbrakk> \<Longrightarrow> (t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'"
  shows "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> (\<gamma>' \<uu> \<gamma>)"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  show ?thesis
  proof cases
    assume "\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
    with `(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>`
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>"
      using validCE_act[of "(t,n')" c t' \<gamma>] by simp
    moreover have "the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>) \<le> the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)"
    proof -
      from `n\<le>n'` have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_mono by simp
      moreover have "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
      ultimately show ?thesis by simp
    qed
    moreover have "\<forall>x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>).
      x<the_enat (\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>) \<longrightarrow> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>'"
    proof (rule allI[OF impI[OF impI]])
      fix x assume "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>) \<le> x" and "x < the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)"
      moreover have "the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>) = \<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>" by simp
      ultimately have "x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using nAct_le_proj[of c n' "inf_llist t"]
        by (metis enat_ord_simps(2) less_le_trans)
      hence "\<exists>(n''::nat). x = \<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>" using nAct_exists by simp
      then obtain n''::nat where "x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>" by blast
  
      have "(t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'"
      proof cases
        assume "x=the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
        with `x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>`
          have "\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" and "x = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" by auto
        show ?thesis
        proof cases
          assume "n\<ge>n''"
          with `\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>` have "\<forall>k\<ge>n''. k<n \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
            using nAct_same_not_active[of c "(enat n)" t "enat n''"] by simp
          moreover from `x=\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>` `x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))`
            have "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active[of x c "inf_llist t" n] by simp
          moreover have "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'"
          proof -
            from `the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>) \<le> x` and `x < the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)`
            have "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>) < the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)" by simp
            moreover have "\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
            moreover have "\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
            ultimately have "\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>" by fastforce
            hence "\<exists>i''\<ge>n. i''<n' \<and> \<parallel>c\<parallel>\<^bsub>t i''\<^esub>" using nAct_not_same_active[of c n "inf_llist t" n'] by simp
            thus ?thesis using a1[of n] by auto
          qed
          ultimately show ?thesis using `n\<ge>n''` validity2[of n'' n c t t' \<gamma>'] by simp
        next
          assume "\<not>n\<ge>n''"
          hence "n\<le>n''" by simp                
          with `\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>` have "\<forall>k\<ge>n. k<n'' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
            using nAct_same_not_active[of c "(enat n'')" t "enat n"] by simp                
          moreover from `x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>` `x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))`
            have "\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active[of x c "inf_llist t" n''] by simp
          moreover have "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'"
          proof -
            from `the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>) \<le> x` and `x < the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)`
            have "the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>) < the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)" by simp
            moreover have "\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
            moreover have "\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
            ultimately have "\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>" by fastforce
            hence "\<exists>i''\<ge>n. i''<n' \<and> \<parallel>c\<parallel>\<^bsub>t i''\<^esub>" using nAct_not_same_active[of c n "inf_llist t" n'] by simp
            thus ?thesis using a1[of n] by auto
          qed
          ultimately show ?thesis using `n''\<ge>n` validity1[of n n'' c t t' \<gamma>'] by simp
        qed
      next
        assume "\<not>(x=the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
        with `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)` have "x > the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by simp
        moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
        ultimately have "x > \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" by fastforce
        with `x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>` have "enat n''\<ge>enat n"
          using nAct_mono_back[of c "(enat n)" "(inf_llist t)" "enat n''"] by simp
        moreover have "\<exists>i''\<ge>n''. i''<n' \<and> \<parallel>c\<parallel>\<^bsub>t i''\<^esub>"
        proof -
          have "\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
          hence "the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>) = \<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>" by simp
          with `x < the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)` and `x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>`
            have "\<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle><\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>" by (metis enat_ord_simps(2))
          thus ?thesis using nAct_not_same_active[of c n'' "inf_llist t" n'] by simp
        qed
        ultimately show ?thesis using a1[of n''] by auto
      qed
      moreover from `x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>` `x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))`
        have "\<exists>i. n'' \<le> enat i \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active[of x c "inf_llist t" n''] by simp
      ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>'"
        using validCE_act[of "(t,n'')" c t' \<gamma>'] by simp
      with `x = \<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>`
        have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat x) \<Turnstile> \<gamma>'" by simp
      thus "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>'" by simp
    qed
    ultimately
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)) \<Turnstile> (\<gamma>' \<uu> \<gamma>)"
      using valid.simps[of "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"] by auto
    moreover from `\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>` have "\<exists>i'\<ge>n. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by (meson `n'\<ge>n` le_trans less_imp_le)
    ultimately show ?thesis by simp
  next
    assume "\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
    with `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>` have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')) \<Turnstile> \<gamma>"
      using validCE_cont[of c "(t, n')"] by simp
    then show ?thesis
    proof cases
      assume "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
      moreover have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> (\<gamma>' \<uu> \<gamma>)"
      proof -
        have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
        proof -
          from `\<not>(\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "n' \<ge> \<langle>c \<and> t\<rangle>" using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` lActive_less by auto
          hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" using cnf2bhv_ge_llength by simp
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
        moreover have "\<forall>x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>).
          x<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<longrightarrow> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>'"
        proof (rule allI[OF impI[OF impI]])
          fix x assume "x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" and "x<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')"
          show "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>'"
          proof (cases)
            assume "(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
            hence "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
              using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
            then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
            
            with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<langle>c \<and> t\<rangle>\<ge>n" using lActive_greatest by fastforce
            moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<and> t\<rangle>" by simp
            ultimately have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> n" by arith
            moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) < n'"
            proof -
              from `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))-1 \<le> x"
                using \<open>lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close> llength_eq_infty_conv_lfinite by fastforce
              with `x<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')` show ?thesis using c2p_mono_p2c_strict by simp
            qed
            moreover have "\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
            proof -
              from `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
                have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) = Suc (\<langle>c \<and> t\<rangle>)"
                using bhv2cnf_lActive by blast
              moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))`
                have "x \<ge> the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" using the_enat_mono by fastforce
              hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))))"
                  using bhv2cnf_mono[of "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" x] by simp
              ultimately have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> Suc (\<langle>c \<and> t\<rangle>)" by simp
              hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) > \<langle>c \<and> t\<rangle>" by simp
              with `\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>` show ?thesis using lActive_greater_active_all by simp
            qed
            ultimately have "(t, \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'" using a2 by simp
            with `\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)`
              have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))) \<Turnstile> \<gamma>'"
              using validCE_cont[of c "(t,\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" t' \<gamma>'] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
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
            hence "\<exists>(n''::nat). x = \<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>" using nAct_exists by simp
            then obtain n''::nat where "x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>" by blast
  
            have "(t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'"
            proof cases
              assume "x=the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
              with `x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>`
                have "\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" and "x = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" by auto
              show ?thesis
              proof cases
                assume "n\<ge>n''"
                with `\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>` have "\<forall>k\<ge>n''. k<n \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
                  using nAct_same_not_active[of c "(enat n)" t "enat n''"] by simp
                moreover have "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'"
                proof -
                  from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` \<open>\<not> (\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)\<close> have "\<exists>i''\<ge>n. i'' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i''\<^esub>"
                    using leI by blast
                  thus ?thesis using a1 by auto
                qed
                ultimately show ?thesis using `n\<ge>n''` `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validity2[of n'' n c t t' \<gamma>'] by simp
              next
                assume "\<not> n\<ge>n''"
                hence "n\<le>n''" by simp
                with `\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>` have "\<forall>k\<ge>n. k<n'' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
                  using nAct_same_not_active by auto
                moreover from \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close>  have "\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using calculation leI by blast
                moreover have "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'"
                proof -
                  from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` \<open>\<not> (\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)\<close> have "\<exists>i''\<ge>n. i'' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i''\<^esub>"
                    using leI by blast
                  thus ?thesis using a1 by auto
                qed
                ultimately show ?thesis using `n\<le>n''` validity1[of n n'' c t t' \<gamma>'] by simp
              qed
            next
              assume "\<not>(x=the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"
              with `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)` have "x > the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by simp
              moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
              ultimately have "x > \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" by fastforce
              with `x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>` have "enat n''\<ge>enat n"
                using nAct_mono_back[of c "(enat n)" "(inf_llist t)" "enat n''"] by simp
              moreover from \<open>\<not> (\<exists>i'\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)\<close> \<open>enat x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close>
                \<open>enat x = \<langle>c #\<^bsub>enat n''\<^esub> inf_llist t\<rangle>\<close> have "\<exists>i''\<ge>n''. i'' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i''\<^esub>"
                by (metis lnth_inf_llist nAct_less_llength_active not_le)
              then obtain i'' where "i''\<ge>n''" and "i'' < n'" and "\<parallel>c\<parallel>\<^bsub>t i''\<^esub>" by blast
              ultimately show ?thesis using a1[of n''] by simp
            qed
            moreover from `x=\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>` `x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))`
              have "\<exists>i. n'' \<le> enat i \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active[of x c "inf_llist t" n''] by simp
            ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>'"
              using validCE_act[of "(t,n'')" c t' \<gamma>'] by simp
            with `x = \<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>`
              have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat x) \<Turnstile> \<gamma>'" by simp
            thus ?thesis by simp
          qed
        qed
        ultimately show ?thesis using `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')) \<Turnstile> \<gamma>`
          valid.simps[of "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"] by auto
      qed
      ultimately show ?thesis using validCI_act by simp
    next
      assume "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
      moreover have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<Turnstile> (\<gamma>' \<uu> \<gamma>)"
      proof -
        from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using proj_finite2 by simp
        then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
  
        from `n\<le>n'` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" using cnf2bhv_mono by simp
        moreover have "\<forall>x::nat\<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n). x<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<longrightarrow> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>'"
        proof (rule allI[OF impI[OF impI]])
          fix x assume "x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" and "x<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')"
  
          from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` lActive_less by auto
          with `x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> n" using p2c_mono_c2p by simp
          moreover from `\<langle>c \<and> t\<rangle> \<le> n` \<open>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) \<le> x\<close> have "x \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
            using cnf2bhv_ge_llength dual_order.trans by blast
          with `x<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) < n'" using c2p_mono_p2c_strict[of c t x n'] by simp
          moreover from \<open>\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> `\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> n` have "\<not> (\<exists>i''\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i''\<^esub>)" by auto
          ultimately have "(t, \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'" using a2[of "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)"] by simp
          moreover have "\<not> (\<exists>i'\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
          proof -
            from `lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))` `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`
              have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) = Suc (\<langle>c \<and> t\<rangle>)" using bhv2cnf_lActive by blast
            moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "n>\<langle>c \<and> t\<rangle>"
              by (meson `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` lActive_active leI le_eq_less_or_eq)
            hence "n\<ge>Suc (\<langle>c \<and> t\<rangle>)" by simp
            with `x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> n" using p2c_mono_c2p by simp
            with `n\<ge>Suc(\<langle>c \<and> t\<rangle>)` have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> Suc (\<langle>c \<and> t\<rangle>)" by simp
            hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) > \<langle>c \<and> t\<rangle>" by simp
            with `\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>` show ?thesis using lActive_greater_active_all by simp
          qed
          ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))) \<Turnstile> \<gamma>'"
            using validCE_cont[of c "(t,\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" t' \<gamma>'] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
          moreover have "x \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
            using \<open>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) \<le> x\<close> cnf2bhv_def by auto
          ultimately show "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>'"
            using cnf2bhv_bhv2cnf by simp
        qed
        ultimately show ?thesis using `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')) \<Turnstile> \<gamma>`
          valid.simps[of "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>))"] by auto
      qed    
      ultimately show ?thesis using validCI_cont[of c "(t,n)" t' "\<gamma>' \<uu> \<gamma>"] by (simp add: `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>`)
    qed
  qed
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms show ?thesis using validC_def by auto
qed

lemma bUntilEA:
  fixes n::nat
    and n'::nat
    and t::CTraceINF
    and t'::BTraceINF
    and c::cid
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> (\<gamma>' \<uu> \<gamma>)"
  shows "\<exists>n'\<ge>\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub>. ((t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>) \<and>
    (\<forall>n''\<ge>n. (\<exists>i'\<ge>n''. i' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< n') \<longrightarrow> ((t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'))"
proof -
  from assms have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)) \<Turnstile> (\<gamma>' \<uu> \<gamma>)"
    using validCE_act[of "(t,n)" c t' "\<gamma>' \<uu> \<gamma>"] by simp
  then obtain x where "x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
    and "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>"
    and "\<forall>x'\<ge>the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>). x'<x \<longrightarrow> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x') \<Turnstile> \<gamma>'"
    by auto
  show ?thesis
  proof (cases)
    assume "(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
    moreover from `(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>" by (metis infinity_ileE)
    moreover from `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<ge>1" using proj_one[of "inf_llist t"] by auto
    ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x"
      by (metis One_nat_def Suc_ile_eq antisym_conv2 diff_Suc_less
          enat_ord_simps(2) enat_the_enat less_imp_diff_less one_enat_def) (*Refactor*)
    hence "x = \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" using cnf2bhv_bhv2cnf by simp
    with `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>`
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))) \<Turnstile> \<gamma>" by simp
    moreover have "\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
    proof -
      from `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
      then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
      moreover from `the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x` have "\<langle>c \<and> t\<rangle> < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)"
        using bhv2cnf_greater_lActive by simp
      ultimately show ?thesis using lActive_greater_active_all by simp
    qed
    ultimately have "validC (t,\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)) t' c \<gamma>"
      using `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` validCI_cont[of c "(t,\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))"] by fastforce
    moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<or> t\<rangle>\<^bsub>n\<^esub>"
    proof -
      from `x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using llength_geq_enat_lfiniteD[of "\<pi>\<^bsub>c\<^esub>(inf_llist t)" x] by simp
      then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
      with `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<langle>c \<and> t\<rangle>\<ge>n" using lActive_greatest by fastforce
      moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> \<langle>c \<and> t\<rangle>" by simp
      ultimately have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<ge> n" by arith
      thus ?thesis using lNactLe by (metis HOL.no_atp(11))
    qed
    moreover have "\<forall>n''\<ge>n. ((\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)))
      \<longrightarrow> ((t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>')"
    proof (rule allI[OF impI[OF impI]])
      fix n'' assume "n''\<ge>n" and "(\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))"
      show "(t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'"
      proof cases
        assume "\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
        hence "the_enat(\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
          by (metis Extended_Nat.eSuc_mono eSuc_enat enat.distinct(2)
              iless_Suc_eq nAct_enat_the_nat nAct_llength_proj)
        with \<open>llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) \<le> enat x\<close> have "the_enat(\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) < x"
          using enat_ord_simps(2) less_le_trans by blast
        moreover from `n''\<ge>n` have "the_enat(\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) \<ge> the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
          using nAct_mono by simp
        ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>'"
          using `\<forall>x'\<ge>the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>). x'<x \<longrightarrow>
          (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x') \<Turnstile> \<gamma>'` by simp
        moreover from `\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>` have "\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by auto
        ultimately show "(t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'" using validCI_act[of "(t, n'')" c t' \<gamma>'] by simp
      next
        assume "\<not>(\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
        with `(\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))`
          have "n''<\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)" by simp
        hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'') < x"
          using \<open>the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x\<close> \<open>x = \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))\<close> cnf2bhv_def by auto (*Lemma*)
        moreover have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'') \<ge> the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
        proof -
          from \<open>(\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> \<not> (\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n'' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)\<close>
            \<open>\<not> (\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)\<close> have "\<not> (\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)" by simp
          hence "\<langle>c \<and> t\<rangle> < n''" by (meson assms(1) lActive_active leI less_or_eq_imp_le)
          hence "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'')" using cnf2bhv_greater_llength by simp
          hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'') \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" by simp
          with `llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<noteq>\<infinity>` have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'') \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" by auto
          hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'') \<ge> \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" using nAct_le_proj[of c n "inf_llist t"] by simp
          moreover have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
          ultimately show ?thesis by fastforce
        qed
        ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'')) \<Turnstile> \<gamma>'" using
          `\<forall>x'\<ge>the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>). x'<x \<longrightarrow> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x') \<Turnstile> \<gamma>'`
          by simp
        moreover from `\<not>(\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)` have "\<not> (\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
          using `\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` leI by blast
        ultimately show "(t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'" using validCI_cont[of c "(t, n'')" t' \<gamma>'] `\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by fastforce
      qed
    qed      
    ultimately show ?thesis by blast
  next
    assume "\<not>(x \<ge> llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
    hence "x<llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))" by simp
    then obtain n'::nat where "x=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_exists by blast
    moreover have "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
    ultimately have "x=the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)" by fastforce
    with `(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>`
      have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>" by simp
    moreover from \<open>enat x < llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close> \<open>enat x = \<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>\<close>
      have "\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using nAct_less_llength_active by force
    ultimately have "(t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" using validCI_act by simp
    moreover have "n'\<ge>\<langle>c \<or> t\<rangle>\<^bsub>n\<^esub>"
    proof cases
      assume "n'\<ge>n"
      thus ?thesis using lNactLe by (metis HOL.no_atp(11))
    next
      assume "\<not>n'\<ge>n"
      hence "n'<n" by simp
      with `x\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)` have "x=the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
        by (simp add: \<open>x = the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>)\<close> dual_order.antisym nAct_mono)
      with `x=the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)`
        have "the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)=the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)" by simp
      hence "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>=\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" by (metis enat.distinct(2) nAct_enat_the_nat)
      with `n'<n` have "\<not> \<parallel>c\<parallel>\<^bsub>t n'\<^esub>" using nAct_same_not_active[of c n t n'] by simp
      with `n'<n` show ?thesis using lNactLe by auto
    qed
    moreover have "\<forall>n''\<ge>n. ((\<exists>i'\<ge>n''. i' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< n'))
      \<longrightarrow> ((t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>')"
    proof (rule allI[OF impI[OF impI]])
      fix n'' assume "n''\<ge>n" and "(\<exists>i'\<ge>n''. i' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< n')"
      hence "the_enat(\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) \<ge> the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)" by (simp add: nAct_mono)
      moreover have "the_enat(\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) < the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)"
      proof -
        from `(\<exists>i'\<ge>n''. i' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< n')` have "n''\<le>n'" by auto
        with `\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<exists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using le_trans by blast
        with `(\<exists>i'\<ge>n''. i' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< n')`
          have "\<exists>i'\<ge>n''. i' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by simp
        then obtain i' where "i'\<ge>n''" and "i' < n'" and "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by blast
        moreover have "enat i' < llength (inf_llist t)" by simp
        ultimately have "\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>"
          using nAct_less[of i' "inf_llist t" n'' n'] by simp
        thus ?thesis by (metis \<open>enat x = \<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>\<close> less_enatE the_enat.simps)
      qed
      with `x=the_enat(\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>)` have "the_enat(\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>) < x" by simp
      ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), the_enat (\<langle>c #\<^bsub>n''\<^esub> inf_llist t\<rangle>)) \<Turnstile> \<gamma>'"
        using  `\<forall>x'\<ge>the_enat(\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>). x'<x
        \<longrightarrow> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x') \<Turnstile> \<gamma>'` by simp
      moreover from `(\<exists>i'\<ge>n''. i' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< n')`
        have "n''\<le>n'" by auto
      with `\<exists>i\<ge>n'. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` have "\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using order_trans by auto
      ultimately show "(t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'" using validCI_act[of "(t, n'')" c t' \<gamma>'] by simp
    qed
    ultimately show ?thesis by blast
  qed    
qed
  
lemma bUntilEN:
  fixes n::nat
    and n'::nat
    and t::CTraceINF
    and t'::BTraceINF
    and c::cid
  assumes "\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> (\<gamma>' \<uu> \<gamma>)"
  shows "\<exists>n'\<ge>n. ((t, n') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>) \<and>
    (\<forall>n''\<ge>n. (\<exists>i'\<ge>n''. i' < n' \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< n') \<longrightarrow> ((t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'))"
proof cases
  assume "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  with `(t, n) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> (\<gamma>' \<uu> \<gamma>)` have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) \<Turnstile> (\<gamma>' \<uu> \<gamma>)"
    using validCE_cont[of c "(t,n)" t' "(\<gamma>' \<uu> \<gamma>)"] `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` by simp
  then obtain x where "x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" and "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x) \<Turnstile> \<gamma>"
    and "\<forall>x'\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n). x'<x \<longrightarrow> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x') \<Turnstile> \<gamma>'" by auto
  moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x"
  proof -
    from `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using lActive_less[of c t _ n] by auto
    hence "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 \<le> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" using cnf2bhv_ge_llength by simp
    with \<open>\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> \<open>\<not> (\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)\<close> `x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)` show ?thesis
      by (metis cnf2bhv_greater_llength lActive_active leD
          not_le_imp_less order.strict_implies_order order.trans)
  qed
  hence "x = \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" using cnf2bhv_bhv2cnf by simp
  ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))) \<Turnstile> \<gamma>" by simp
  moreover from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<not>(\<exists>i\<ge>\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x). \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  proof -
    from `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using proj_finite2 by simp
    then obtain z where "\<forall>n''>z. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>" using proj_finite_bound by blast
    moreover from `the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 < x` have "\<langle>c \<and> t\<rangle> < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)"
      using bhv2cnf_greater_lActive by simp
    ultimately show ?thesis using lActive_greater_active_all by simp
  qed      
  ultimately have "(t, \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)) \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>" using validCI_cont[of c "(t, \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" t' \<gamma>] `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
  moreover from `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` `\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)` have "\<langle>c \<and> t\<rangle> \<le> n" using lActive_less[of c t _ n] by auto
  with `x\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)` have "n \<le> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)" using p2c_mono_c2p by blast  
  moreover have "\<forall>n''\<ge>n. ((\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> ((\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n''< \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)))
    \<longrightarrow> ((t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>')"
  proof (rule allI[OF impI[OF impI]])
    fix n'' assume "n \<le> n''" and "(\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> \<not> (\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n'' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)"
    hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'')\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)" using cnf2bhv_mono by simp
    moreover from `(\<exists>i'\<ge>n''. i' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x) \<and> \<parallel>c\<parallel>\<^bsub>t i'\<^esub>) \<or> \<not> (\<exists>i\<ge>n''. \<parallel>c\<parallel>\<^bsub>t i\<^esub>) \<and> n'' < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)`
      have "n''<\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x)" by (metis dual_order.strict_trans2)
    with \<open>\<langle>c \<and> t\<rangle> \<le> n\<close> \<open>n \<le> n''\<close> have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'')<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))" using cnf2bhv_mono_strict by simp
    with \<open>x = \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(x))\<close> have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'')< x" by simp
    ultimately have "(lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'')) \<Turnstile> \<gamma>'"
      using `\<forall>x'\<ge>\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n). x'<x \<longrightarrow> (lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')), x') \<Turnstile> \<gamma>'` by simp
    moreover from `n \<le> n''` have "\<nexists>i. i\<ge>n'' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>" using `\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
    ultimately show "(t, n'') \<Turnstile>\<^bsub>t'\<^esub>\<^bsup>c\<^esup> \<gamma>'" using validCI_cont[of c "(t, n'')" t' \<gamma>'] using `\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>` by simp
  qed
  ultimately show ?thesis by auto
next
  assume "\<not>(\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  with assms show ?thesis using validC_def by auto
qed

end