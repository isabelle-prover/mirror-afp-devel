section \<open>Preliminaries\<close>

subsection \<open>Labeled Transition Systems\<close>

theory Transition_Systems
  imports Main
begin
  
locale lts =
fixes
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<longmapsto>_  _" [70, 70, 70] 80)

begin

abbreviation step_pred :: \<open>'s \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool\<close>
  where
  \<open>step_pred p af q \<equiv> \<exists> a. af a \<and> trans p a q\<close>

inductive steps :: \<open>'s \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool\<close>
     ("_ \<longmapsto>* _  _" [70, 70, 70] 80)
where
  refl: \<open>p \<longmapsto>* A p\<close> | step: \<open>p \<longmapsto>* A q1 \<Longrightarrow> q1 \<longmapsto>a q \<Longrightarrow> A a \<Longrightarrow> (p \<longmapsto>* A q)\<close>

lemma steps_one_step: 
  assumes
    \<open>p \<longmapsto>a p'\<close>
     \<open>A a\<close>
   shows
    \<open>p \<longmapsto>* A p'\<close> using steps.step[of p A p a p'] steps.refl[of p A] assms .

lemma steps_concat: 
  assumes
    \<open>p' \<longmapsto>* A p''\<close>
     \<open>p \<longmapsto>* A p'\<close>
   shows
    \<open>p \<longmapsto>* A p''\<close> using assms
proof (induct arbitrary: p)
  case (refl p'' A p')
  then show ?case by auto
next
  case (step p' A p'' a pp p)
  hence \<open>p \<longmapsto>* A  p''\<close> by simp
  show ?case using steps.step[OF `p \<longmapsto>* A  p''` step(3,4)] .
qed

lemma steps_left:
  assumes
    \<open>p \<noteq> p'\<close>
     \<open>p \<longmapsto>* A p'\<close>
   shows
    \<open>\<exists>p'' a . p \<longmapsto>a p'' \<and> A a \<and> p'' \<longmapsto>* A p'\<close>
   using assms(1) 
  by (induct rule:steps.induct[OF assms(2)], blast, metis refl steps_concat steps_one_step) 

lemma steps_no_step:
  assumes
    \<open>\<And> a p' . p \<longmapsto>a p' \<Longrightarrow> \<not>A a\<close>
     \<open>p \<noteq> p''\<close>
     \<open>p \<longmapsto>* A p''\<close>
   shows
    \<open>False\<close>
   using steps_left[OF assms(2,3)] assms(1) by blast
    
lemma steps_no_step_pos:
  assumes
    \<open>\<And> a p' . p \<longmapsto>a p' \<Longrightarrow> \<not>A a\<close>
     \<open>p \<longmapsto>* A p'\<close>
   shows
    \<open>p = p'\<close>
   using assms steps_no_step by blast
    
lemma steps_loop:
  assumes
    \<open>\<And> a p' . p \<longmapsto>a p' \<Longrightarrow> p = p'\<close>
     \<open>p \<noteq> p''\<close>
     \<open>p \<longmapsto>* A p''\<close>
   shows
    \<open>False\<close>
   using assms(3,1,2) by (induct, auto)

corollary steps_transp:
  \<open>transp (\<lambda> p p'. p \<longmapsto>* A p')\<close>
   using steps_concat unfolding transp_def by blast
  
lemma steps_spec: 
  assumes
    \<open>p \<longmapsto>* A' p'\<close>
     \<open>\<And> a . A' a \<Longrightarrow> A a\<close>
   shows
    \<open>p \<longmapsto>* A p'\<close> using assms(1,2)
proof induct
  case (refl p)
  show ?case using steps.refl .
next
  case (step p A' pp a pp')
  hence \<open>p \<longmapsto>* A  pp\<close> by simp 
  then show ?case using step(3,4,5) steps.step by auto
qed

interpretation preorder \<open>(\<lambda> p p'. p \<longmapsto>* A p')\<close> \<open>\<lambda> p p'. p \<longmapsto>* A p' \<and> \<not>(p' \<longmapsto>* A p)\<close>
  by (standard, simp, simp add: steps.refl, metis steps_concat)

text\<open>If one can reach only a finite portion of the graph following @{text \<open>\<longmapsto>* A\<close>},
  and all cycles are loops, then there must be nodes which are maximal wrt. \<open>\<longmapsto>* A\<close>.\<close>
lemma step_max_deadlock:
  fixes A q
  assumes
    antiysmm: \<open>\<And> r1 r2. r1 \<longmapsto>* A r2 \<and> r2 \<longmapsto>* A r1 \<Longrightarrow> r1 = r2\<close> and
    finite: \<open>finite {q'. q \<longmapsto>* A q'}\<close> and
    no_max: \<open>\<forall> q'. q \<longmapsto>* A q' \<longrightarrow> (\<exists>q''. q' \<longmapsto>* A q'' \<and> q' \<noteq> q'')\<close>
   shows
    False
proof -
  interpret order \<open>(\<lambda> p p'. p \<longmapsto>* A p')\<close> \<open>\<lambda> p p'. p \<longmapsto>* A p' \<and> \<not>(p' \<longmapsto>* A p)\<close>
    by (standard, simp add: assms(1))
  show ?thesis using assms order_trans order_refl finite_has_maximal2 mem_Collect_eq
    by metis
qed

end \<comment>\<open>end of lts\<close>

lemma lts_impl_steps2:
  assumes
    \<open>lts.steps step1 p1 ap p2\<close>
     \<open>\<And> p1 a p2 . step1 p1 a p2 \<and> P p1 a p2 \<Longrightarrow> step2 p1 a p2\<close>
     \<open>\<And> p1 a p2 . P p1 a p2\<close>
   shows
    \<open>lts.steps step2 p1 ap p2\<close>
proof (induct rule: lts.steps.induct[OF assms(1)])
  case (1 p af)
  show ?case using lts.steps.refl[of step2 p af] by blast
next
  case (2 p af q1 a q)
  hence \<open>step2 q1 a q\<close> using assms(2,3) by blast
  thus ?case using lts.step[OF 2(2) _ 2(4)] by blast
qed 
  
lemma lts_impl_steps:
  assumes
    \<open>lts.steps step1 p1 ap p2\<close>
     \<open>\<And> p1 a p2 . step1 p1 a p2 \<Longrightarrow> step2 p1 a p2\<close>
   shows
    \<open>lts.steps step2 p1 ap p2\<close>
   using assms lts_impl_steps2[OF assms] by auto
  
end