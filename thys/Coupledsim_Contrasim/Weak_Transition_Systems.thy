subsection \<open>Transition Systems with Silent Steps\<close>

theory Weak_Transition_Systems
  imports Transition_Systems
begin                

locale lts_tau = lts trans for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<longmapsto>_  _" [70, 70, 70] 80) + fixes
  \<tau> :: \<open>'a\<close> begin
  
definition tau :: \<open>'a \<Rightarrow> bool\<close> where \<open>tau a \<equiv> (a = \<tau>)\<close>

lemma tau_tau[simp]: \<open>tau \<tau>\<close> unfolding tau_def by simp

abbreviation weak_step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
     ("_ \<Rightarrow>_  _" [70, 70, 70] 80)
where
  \<open>(p \<Rightarrow>a q) \<equiv> (\<exists> pq1 pq2.
    p \<longmapsto>* tau pq1 \<and>
    pq1 \<longmapsto>a   pq2 \<and>
    pq2 \<longmapsto>* tau q)\<close>

lemma step_weak_step:
  assumes \<open>p \<longmapsto>a p'\<close>
   shows   \<open>p \<Rightarrow>a p'\<close>
   using assms steps.refl by auto
    
abbreviation weak_step_tau :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
     ("_ \<Rightarrow>^_  _" [70, 70, 70] 80)
where
  \<open>(p \<Rightarrow>^a q) \<equiv>
    (tau a \<longrightarrow> p \<longmapsto>* tau q) \<and>
    (\<not>tau a \<longrightarrow> p \<Rightarrow>a q)\<close>

abbreviation weak_step_delay :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
     ("_ =\<rhd> _  _" [70, 70, 70] 80)
where
  \<open>(p =\<rhd>a q) \<equiv> 
    (tau a \<longrightarrow> p \<longmapsto>* tau q) \<and>
    (\<not>tau a \<longrightarrow>  (\<exists> pq.
      p \<longmapsto>* tau pq \<and>
      pq \<longmapsto>a   q))\<close>

lemma weak_step_delay_implies_weak_tau:
  assumes \<open>p =\<rhd>a p'\<close>
  shows \<open>p \<Rightarrow>^a p'\<close>
  using assms steps.refl[of p' tau] by blast

lemma weak_step_delay_left:
  assumes
    \<open>\<not> p0 \<longmapsto>a p1\<close>
    \<open>p0 =\<rhd>a p1\<close>
    \<open>\<not>tau a\<close>
  shows
    \<open>\<exists> p0' t. tau t \<and> p0 \<longmapsto>t p0' \<and> p0' =\<rhd>a p1\<close>
  using assms steps_left by metis

primrec weak_step_seq :: \<open>'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool\<close>
     ("_ \<Rightarrow>$ _  _" [70, 70, 70] 80)
  where
    \<open>weak_step_seq p0 [] p1 = p0 \<longmapsto>* tau p1\<close>
  | \<open>weak_step_seq p0 (a#A) p1 = (\<exists> p01 . p0 \<Rightarrow>^a p01 \<and> weak_step_seq p01 A p1)\<close>

lemma step_weak_step_tau:
  assumes \<open>p \<longmapsto>a p'\<close>
  shows   \<open>p \<Rightarrow>^a p'\<close>
  using step_weak_step[OF assms] steps_one_step[OF assms]
  by blast
    
lemma step_tau_refl:
  shows   \<open>p \<Rightarrow>^\<tau> p\<close>
  using steps.refl[of p tau]
  by simp
    
lemma weak_step_tau_weak_step[simp]:
  assumes \<open>p \<Rightarrow>^a p'\<close> \<open>\<not> tau a\<close>
  shows   \<open>p \<Rightarrow>a p'\<close>
  using assms by auto
  
lemma weak_steps:
  assumes
    \<open>p \<Rightarrow>a  p'\<close>
    \<open>\<And> a . tau a \<Longrightarrow> A a\<close>
    \<open>A a\<close>
  shows
    \<open>p \<longmapsto>* A  p'\<close>
proof -
  obtain pp pp' where pp:
    \<open>p \<longmapsto>* tau pp\<close> \<open>pp \<longmapsto>a  pp'\<close> \<open>pp' \<longmapsto>* tau p'\<close>
     using assms(1) by blast
  then have cascade:
    \<open>p \<longmapsto>* A pp\<close> \<open>pp \<longmapsto>* A  pp'\<close> \<open>pp' \<longmapsto>* A p'\<close>
     using steps_one_step steps_spec assms(2,3) by auto
  have \<open>p \<longmapsto>* A pp'\<close> using steps_concat[OF cascade(2) cascade(1)] .
  show ?thesis using steps_concat[OF cascade(3) `p \<longmapsto>* A  pp'`] .
qed
  
lemma weak_step_impl_weak_tau:
  assumes
    \<open>p \<Rightarrow>a p'\<close>
  shows
    \<open>p \<Rightarrow>^a p'\<close>
  using assms weak_steps[OF assms, of tau] by auto
  
lemma weak_impl_strong_step:
  assumes
    \<open>p \<Rightarrow>a  p''\<close>
  shows
    \<open>(\<exists> a' p' . tau a' \<and> p \<longmapsto>a'  p') \<or> (\<exists> p' . p \<longmapsto>a  p')\<close>
proof  -
  from assms obtain pq1 pq2 where pq12:
    \<open>p \<longmapsto>* tau pq1\<close>
     \<open>pq1 \<longmapsto>a   pq2\<close>
     \<open>pq2 \<longmapsto>* tau p''\<close> by blast
  show ?thesis
  proof (cases \<open>p = pq1\<close>)
    case True
    then show ?thesis using pq12 by blast
  next
    case False
    then show ?thesis using pq12 steps_left[of p pq1 tau] by blast
  qed
qed
  
lemma weak_step_extend:
  assumes 
    \<open>p1 \<longmapsto>* tau p2\<close>
    \<open>p2 \<Rightarrow>^a p3\<close>
    \<open>p3 \<longmapsto>* tau p4\<close>
  shows
    \<open>p1 \<Rightarrow>^a p4\<close>
  using assms steps_concat by blast
    
lemma weak_step_tau_tau:
  assumes 
    \<open>p1 \<longmapsto>* tau p2\<close>
    \<open>tau a\<close>
  shows
    \<open>p1 \<Rightarrow>^a p2\<close>
  using assms by blast

lemma weak_single_step[iff]: 
  \<open>p \<Rightarrow>$ [a] p' \<longleftrightarrow> p \<Rightarrow>^a  p'\<close>
   using steps.refl[of p' tau]
  by (meson steps_concat weak_step_seq.simps(1) weak_step_seq.simps(2))

abbreviation weak_enabled :: \<open>'s \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>weak_enabled p a \<equiv>
    \<exists> pq1 pq2. p \<longmapsto>* tau pq1 \<and> pq1 \<longmapsto>a pq2\<close>

lemma weak_enabled_step:
  shows \<open>weak_enabled p a = (\<exists> p'. p \<Rightarrow>a p')\<close>
  using step_weak_step steps_concat by blast

lemma step_tau_concat: 
  assumes 
    \<open>q \<Rightarrow>^a q'\<close>
    \<open>q' \<Rightarrow>^\<tau> q1\<close>
  shows \<open>q \<Rightarrow>^a q1\<close>
proof - 
  show ?thesis using assms steps_concat tau_tau by blast 
qed

lemma tau_step_concat: 
  assumes 
    \<open>q \<Rightarrow>^\<tau> q'\<close>
    \<open>q' \<Rightarrow>^a q1\<close>
  shows \<open>q \<Rightarrow>^a q1\<close>
proof - 
  show ?thesis using assms steps_concat tau_tau by blast 
qed


lemma tau_word_concat: 
  assumes
    \<open>q \<Rightarrow>^\<tau> q'\<close> 
    \<open>q' \<Rightarrow>$A q1\<close> 
  shows \<open>q \<Rightarrow>$A q1\<close>
  using assms
proof (cases A)
  case Nil
  hence \<open>q' \<Rightarrow>^\<tau> q1\<close> using assms by auto
  thus ?thesis using Nil assms steps_concat tau_tau weak_step_seq.simps by blast
next
  case (Cons a A)
  then obtain q'' where  \<open>q' \<Rightarrow>^a q''\<close> and A_step:  \<open>q'' \<Rightarrow>$A q1 \<close> using assms by auto
  hence \<open>q \<Rightarrow>^a q''\<close> using tau_step_concat[OF assms(1)] by auto
  then show ?thesis using Cons A_step  \<open>q \<Rightarrow>^a q''\<close> by auto 
qed

lemma strong_weak_transition_system:
  assumes
    \<open>\<And> p q a. p \<longmapsto> a q \<Longrightarrow> \<not> tau a\<close>
    \<open>\<not> tau a\<close>
  shows
    \<open>p \<Rightarrow>^a p' = p \<longmapsto> a p'\<close>
proof
  assume \<open>p \<Rightarrow>^a  p'\<close>
  then obtain p0 p1 where \<open>p \<longmapsto>* tau p0\<close> \<open>p0 \<longmapsto>a p1\<close> \<open>p1 \<longmapsto>* tau p'\<close> using assms by blast
  then have \<open>p = p0\<close> \<open>p1 = p'\<close> using assms(1) steps_no_step by blast+
  with \<open>p0 \<longmapsto>a p1\<close> show \<open>p \<longmapsto>a  p'\<close> by blast
next
  assume \<open>p \<longmapsto>a  p'\<close>
  thus \<open>p \<Rightarrow>^a  p'\<close> using step_weak_step_tau by blast
qed

lemma rev_seq_split : 
  assumes \<open>q \<Rightarrow>$ (xs @ [x])  q1\<close>
  shows \<open>\<exists>q'. q \<Rightarrow>$xs q' \<and> q' \<Rightarrow>^x q1\<close>
  using assms
proof (induct xs arbitrary: q)
  case Nil
  hence \<open>q \<Rightarrow>$ [x]  q1\<close> by auto
  hence x_succ: \<open>q \<Rightarrow>^x q1\<close> by blast 
  have \<open>q \<Rightarrow>$[] q\<close> by (simp add: steps.refl) 
  then show ?case using x_succ by auto
next
  case (Cons a xs)
  then obtain q' where q'_def: \<open>q \<Rightarrow>^a q' \<and> q' \<Rightarrow>$(xs@[x]) q1\<close> by auto
  then obtain q'' where \<open>q' \<Rightarrow>$ xs  q'' \<and> q'' \<Rightarrow>^x  q1\<close> using Cons.hyps[of \<open>q'\<close>] by auto
  then show ?case using q'_def by auto
qed

lemma rev_seq_concat: 
  assumes 
    \<open>q \<Rightarrow>$as q'\<close> 
    \<open>q'\<Rightarrow>$A q1\<close>
  shows \<open>q \<Rightarrow>$(as@A) q1\<close>
  using assms
proof (induct as arbitrary: A q' rule: rev_induct)
  case Nil
  hence \<open>q \<Rightarrow>^\<tau> q'\<close> by auto
  hence \<open>q \<Rightarrow>^\<tau> q' \<and> q' \<Rightarrow>$A q1\<close> using Nil.prems(2) by blast 
  hence \<open>q \<Rightarrow>$A q1\<close> using tau_word_concat by auto 
  then show ?case by simp
next
  case (snoc x xs)
  hence \<open>\<exists>q''. q \<Rightarrow>$xs q'' \<and> q'' \<Rightarrow>^x q'\<close> using rev_seq_split by simp
  then obtain q'' where q_def: \<open>q \<Rightarrow>$xs q''\<close> \<open>q'' \<Rightarrow>^x q'\<close> by auto
  from snoc.prems(2) have \<open>q' \<Rightarrow>$A q1\<close> by blast
  hence \<open>q'' \<Rightarrow>$(x#A) q1\<close> using q_def by auto
  hence \<open>q'' \<Rightarrow>$([x]@A) q1\<close> by auto
  then show ?case using snoc.hyps[of \<open>q''\<close> \<open>[x]@A\<close>] q_def by auto
qed

lemma rev_seq_step_concat : 
  assumes 
    \<open>q \<Rightarrow>$as q'\<close> 
    \<open>q'\<Rightarrow>^a q1\<close>
  shows \<open>q \<Rightarrow>$(as@[a]) q1\<close>
proof - 
  from assms(2) have \<open>q'\<Rightarrow>$[a] q1\<close> by blast
  thus ?thesis using rev_seq_concat assms(1) by auto
qed

lemma rev_seq_dstep_concat : 
  assumes 
    \<open>q \<Rightarrow>$as q'\<close> 
    \<open>q'=\<rhd>a q1\<close>
  shows \<open>q \<Rightarrow>$(as@[a]) q1\<close>
proof - 
  from assms(2) have \<open>q' \<Rightarrow>^a q1\<close> using steps.refl by auto
  thus ?thesis using assms rev_seq_step_concat by auto
qed

lemma word_tau_concat: 
  assumes 
    \<open>q \<Rightarrow>$A q'\<close>
    \<open>q' \<Rightarrow>^\<tau> q1\<close> 
  shows \<open>q \<Rightarrow>$A q1\<close> 
proof - 
  from assms(2) have \<open>q' \<Rightarrow>$[] q1\<close>
    using tau_tau weak_step_seq.simps(1) by blast 
  thus ?thesis using assms(1) rev_seq_concat
    by (metis append.right_neutral) 
qed

lemma list_rev_split : 
  assumes \<open>A \<noteq> []\<close>
  shows \<open>\<exists>as a. A = as@[a]\<close>
proof - 
  show ?thesis using assms rev_exhaust by blast 
qed

primrec taufree :: \<open>'a list \<Rightarrow> 'a list\<close>
  where
    \<open>taufree [] = []\<close>
  | \<open>taufree (a#A) = (if tau a then taufree A else a#(taufree A))\<close>

lemma weak_step_over_tau : 
  assumes 
    \<open>p \<Rightarrow>$A p'\<close>
  shows \<open>p \<Rightarrow>$(taufree A) p'\<close> using assms
proof (induct A arbitrary: p)
  case Nil
  thus ?case by auto
next
  case (Cons a as)
  then obtain p0 where \<open>p \<Rightarrow>^a p0\<close> \<open>p0\<Rightarrow>$as p'\<close> by auto
  then show ?case
  proof (cases \<open>tau a\<close>)
    case True
    hence \<open>p \<Rightarrow>$as p'\<close> using tau_word_concat \<open>p \<Rightarrow>^a p0\<close> \<open>p0 \<Rightarrow>$ as p'\<close> tau_tau by blast
    hence \<open>p \<Rightarrow>$ (taufree as)  p'\<close> using Cons by auto
    thus \<open>p \<Rightarrow>$ (taufree (a#as))  p'\<close> using True by auto
  next
    case False
    hence rec: \<open>taufree (a#as) = a#(taufree as)\<close> by auto
    hence \<open>p0 \<Rightarrow>$ (taufree as)  p'\<close> using \<open>p0\<Rightarrow>$as p'\<close> Cons by auto
    hence \<open>p \<Rightarrow>$(a#(taufree as)) p'\<close> using  \<open>p \<Rightarrow>^a p0\<close> by auto
    then show ?thesis using rec by auto
  qed
qed

lemma app_tau_taufree_list : 
  assumes 
    \<open>\<forall>a \<in> set A. \<not>tau a\<close>
    \<open>b = \<tau>\<close>
  shows \<open>A = taufree (A@[b])\<close> using assms(1)
proof (induct A)
  case Nil
  then show ?case using assms by simp
next
  case (Cons x xs)
  have \<open>\<forall>a\<in>set xs. \<not> tau a\<close> \<open>\<not>tau x\<close> using assms(1) butlast_snoc Cons by auto 
  hence last: \<open>xs = taufree (xs @ [b])\<close> using Cons by auto
  have \<open>taufree (x#xs@[b]) = x#taufree (xs @ [b])\<close> using \<open>\<not>tau x\<close> by auto
  hence \<open>x # xs = x# taufree (xs@ [b])\<close> using last by auto
  then show ?case using Cons.prems last by auto
qed

lemma word_steps_ignore_tau_addition:
  assumes
    \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close>
    \<open>p \<Rightarrow>$ A p'\<close>
    \<open>filter (\<lambda>a. a \<noteq> \<tau>) A' = A\<close>
  shows
    \<open>p \<Rightarrow>$ A' p'\<close>
  using assms
proof (induct A' arbitrary: p A)
  case Nil': Nil
  then show ?case by simp
next
  case Cons': (Cons a' A' p)
  show ?case proof (cases \<open>a' = \<tau>\<close>)
    case True
    with Cons'.prems have \<open>filter (\<lambda>a. a \<noteq> \<tau>) A' = A\<close> by simp
    with Cons' have \<open>p \<Rightarrow>$ A' p'\<close> by blast
    with True show ?thesis using steps.refl by fastforce
  next
    case False
    with Cons'.prems obtain A'' where
      A''_spec: \<open>A = a'#A''\<close> \<open>filter (\<lambda>a. a \<noteq> \<tau>) A' = A''\<close> \<open>\<forall>a\<in>set A''. a \<noteq> \<tau> \<close> by auto
    with Cons'.prems obtain p0 where
      p0_spec: \<open>p \<Rightarrow>^a' p0\<close> \<open>p0 \<Rightarrow>$ A'' p'\<close> by auto
    with Cons'.hyps A''_spec(2,3) have \<open>p0 \<Rightarrow>$ A'  p'\<close> by blast
    with p0_spec show ?thesis by auto
  qed
qed

lemma word_steps_ignore_tau_removal:
  assumes
    \<open>p \<Rightarrow>$ A p'\<close>
  shows
    \<open>p \<Rightarrow>$ (filter (\<lambda>a. a \<noteq> \<tau>) A) p'\<close>
  using assms
proof (induct A arbitrary: p)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  show ?case proof (cases \<open>a = \<tau>\<close>)
    case True
    with Cons show ?thesis using tau_word_concat by auto
  next
    case False
    with Cons.prems obtain p0 where p0_spec: \<open>p \<Rightarrow>^a p0\<close> \<open>p0 \<Rightarrow>$ A p'\<close> by auto
    with Cons.hyps have \<open>p0 \<Rightarrow>$ (filter (\<lambda>a. a \<noteq> \<tau>) A) p'\<close> by blast
    with \<open>p \<Rightarrow>^a p0\<close> False show ?thesis by auto
  qed
qed

definition weak_tau_succs :: "'s set \<Rightarrow> 's set" where
  \<open>weak_tau_succs Q  = {q1. \<exists>q\<in> Q. q \<Rightarrow>^\<tau> q1}\<close> 

definition dsuccs :: "'a \<Rightarrow> 's set \<Rightarrow> 's set" where
  \<open>dsuccs a Q  = {q1. \<exists>q\<in> Q. q =\<rhd>a q1}\<close> 

definition word_reachable_via_delay :: "'a list \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  \<open>word_reachable_via_delay A p p0 p1 = (\<exists>p00. p \<Rightarrow>$(butlast A) p00 \<and> p00 =\<rhd>(last A) p0 \<and> p0 \<Rightarrow>^\<tau> p1)\<close>

primrec dsuccs_seq_rec :: "'a list \<Rightarrow> 's set \<Rightarrow> 's set" where
  \<open>dsuccs_seq_rec [] Q  = Q\<close> | 
  \<open>dsuccs_seq_rec (a#as) Q  = dsuccs a (dsuccs_seq_rec as Q)\<close>

lemma in_dsuccs_implies_word_reachable:
  assumes 
    \<open>q' \<in> dsuccs_seq_rec (rev A) {q}\<close>
  shows
    \<open>q \<Rightarrow>$A q'\<close>
  using assms
proof (induct arbitrary: q' rule: rev_induct) 
  case Nil
  hence \<open>q' = q\<close> by auto
  hence \<open>q \<Rightarrow>^\<tau> q'\<close> by (simp add: steps.refl) 
  thus \<open>q \<Rightarrow>$[] q'\<close> by simp
next
  case (snoc a as)
  hence \<open>q' \<in> dsuccs_seq_rec (a#(rev as)) {q}\<close> by simp
  hence \<open>q' \<in> dsuccs a (dsuccs_seq_rec (rev as) {q})\<close> by simp
  then obtain q0 where \<open>q0 \<in> dsuccs_seq_rec (rev as) {q}\<close> 
    and \<open>q0 =\<rhd>a q'\<close> using dsuccs_def  by auto
  hence \<open>q \<Rightarrow>$as q0\<close> using snoc.hyps by auto
  thus \<open>q \<Rightarrow>$(as @ [a]) q'\<close> 
    using \<open>q0 =\<rhd>a q'\<close> steps.refl rev_seq_step_concat by blast 
qed

lemma word_reachable_implies_in_dsuccs : 
  assumes 
    \<open>q \<Rightarrow>$A q'\<close>
  shows \<open>q' \<in> weak_tau_succs (dsuccs_seq_rec (rev A) {q})\<close> using assms
proof (induct A arbitrary: q' rule: rev_induct)
  case Nil
  hence \<open>q \<Rightarrow>^\<tau> q'\<close> using tau_tau weak_step_seq.simps(1) by blast 
  hence \<open>q' \<in> weak_tau_succs {q}\<close> using weak_tau_succs_def by auto
  thus ?case using dsuccs_seq_rec.simps(1) by auto
next
  case (snoc a as)
  then obtain q1 where \<open>q \<Rightarrow>$as q1\<close> and \<open>q1 \<Rightarrow>^a q'\<close> using rev_seq_split by blast 
  hence in_succs: \<open>q1 \<in> weak_tau_succs (dsuccs_seq_rec (rev as) {q})\<close> using snoc.hyps by auto
  then obtain q0 where q0_def: \<open>q0 \<in> dsuccs_seq_rec (rev as) {q}\<close> \<open>q0 \<Rightarrow>^\<tau> q1\<close> 
    using weak_tau_succs_def[of\<open>dsuccs_seq_rec (rev as) {q}\<close>] by auto
  hence \<open>q0 \<Rightarrow>^a q'\<close> using \<open>q1 \<Rightarrow>^a q'\<close> steps_concat tau_tau by blast 
  then obtain q2 where \<open>q0 =\<rhd>a q2\<close> \<open>q2 \<Rightarrow>^\<tau> q'\<close> using steps.refl by auto 
  hence \<open>\<exists>q0 \<in> dsuccs_seq_rec (rev as) {q}. q0 =\<rhd>a q2\<close> using q0_def by auto
  hence \<open>q2 \<in> dsuccs a (dsuccs_seq_rec (rev as) {q})\<close>  using dsuccs_def by auto
  hence \<open>q2 \<in> dsuccs_seq_rec (a#(rev as)) {q}\<close> by auto
  hence \<open>q2 \<in> dsuccs_seq_rec (rev (as@[a])) {q}\<close> by auto
  hence \<open>\<exists>q2 \<in> dsuccs_seq_rec (rev (as@[a])) {q}. q2 \<Rightarrow>^\<tau> q'\<close> using \<open>q2 \<Rightarrow>^\<tau> q'\<close> by auto
  thus ?case using weak_tau_succs_def[of \<open>dsuccs_seq_rec (rev (as@[a])) {q}\<close>] by auto
qed

lemma simp_dsuccs_seq_rev: 
  assumes 
    \<open>Q = dsuccs_seq_rec (rev A) {q0}\<close>
  shows 
    \<open>dsuccs a Q = dsuccs_seq_rec (rev (A@[a])) {q0}\<close>
proof - 
  show ?thesis by (simp add: assms) 
qed

abbreviation tau_max :: \<open>'s \<Rightarrow> bool\<close> where
  \<open>tau_max p \<equiv>  (\<forall>p'. p \<longmapsto>* tau p' \<longrightarrow> p = p')\<close>

lemma tau_max_deadlock:
  fixes q
  assumes
    \<open>\<And> r1 r2. r1 \<longmapsto>* tau r2 \<and> r2 \<longmapsto>* tau r1 \<Longrightarrow> r1 = r2\<close> \<comment>\<open>contracted cycles (anti-symmetry)\<close>
    \<open>finite {q'. q \<longmapsto>* tau q'}\<close>
  shows
    \<open>\<exists> q' . q \<longmapsto>* tau q' \<and> tau_max q'\<close>
  using step_max_deadlock assms by blast

abbreviation stable_state :: \<open>'s \<Rightarrow> bool\<close> where
  \<open>stable_state p \<equiv> \<nexists> p' . step_pred p tau p'\<close>
   
lemma stable_tauclosure_only_loop:
  assumes
    \<open>stable_state p\<close>
  shows
    \<open>tau_max p\<close>
  using assms  steps_left by blast

coinductive divergent_state :: \<open>'s \<Rightarrow> bool\<close> where
  omega: \<open>divergent_state p' \<Longrightarrow> tau t \<Longrightarrow>  p \<longmapsto>t p'\<Longrightarrow> divergent_state p\<close>
    
lemma ex_divergent:
  assumes \<open>p \<longmapsto>a p\<close> \<open>tau a\<close>
  shows \<open>divergent_state p\<close>
  using assms 
proof (coinduct)
  case (divergent_state p)
  then show ?case using assms by auto
qed
  
lemma ex_not_divergent:
  assumes \<open>\<forall>a q. p \<longmapsto>a q \<longrightarrow> \<not> tau a\<close> \<open>divergent_state p\<close>
  shows \<open>False\<close> using assms(2)
proof (cases rule:divergent_state.cases)
  case (omega p' t)
  thus ?thesis using assms(1) by auto
qed

lemma perpetual_instability_divergence:
  assumes
    \<open>\<forall> p' . p \<longmapsto>* tau p' \<longrightarrow> \<not> stable_state p'\<close>
  shows
    \<open>divergent_state p\<close>
  using assms
proof (coinduct rule: divergent_state.coinduct)
  case (divergent_state p)
  then obtain t p' where \<open>tau t\<close> \<open>p \<longmapsto>t  p'\<close> using steps.refl by blast
  then moreover have \<open>\<forall>p''. p' \<longmapsto>* tau  p'' \<longrightarrow> \<not> stable_state p''\<close>
     using divergent_state step_weak_step_tau steps_concat by blast
  ultimately show ?case by blast 
qed

corollary non_divergence_implies_eventual_stability:
  assumes
    \<open>\<not> divergent_state p\<close>
  shows
    \<open>\<exists> p' . p \<longmapsto>* tau p' \<and> stable_state p'\<close>
  using assms perpetual_instability_divergence by blast

end \<comment>\<open>context @{locale lts_tau}\<close>

subsection \<open>Finite Transition Systems with Silent Steps\<close>

locale lts_tau_finite = lts_tau trans \<tau> for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> +
assumes 
  finite_state_set: \<open>finite (top::'s set)\<close>
begin

lemma finite_state_rel: \<open>finite (top::('s rel))\<close>
  using finite_state_set
  by (simp add: finite_prod)

end

end