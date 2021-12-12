(*by Ammer*)
theory Simple_TBOUND_Cond
imports Time_Reasoning
begin

text \<open>This entry stops at showing the correctness and complexity of the operations,
  but does not provide a complete or universally usable methods to reason about
  programs using these operations. 
  
  In this theory, we provide an ad-hoc method, which is showcased 
  with a simple example later on.
\<close>

text \<open>definition of conditional TBOUND relation  and setup\<close>

definition cond_TBOUND::"assn \<Rightarrow> 'a Heap  \<Rightarrow> nat\<Rightarrow> bool"("\<section> _ \<section>/ TBOUND/ _ _") where
  "cond_TBOUND P c t \<equiv> (\<forall>h as. (h,as) \<Turnstile> P \<longrightarrow> time c h \<le> t)" 

named_theorems cond_TBOUND  

lemma htt_elim:
  assumes "<P> c <Q>T[b]"
  shows "\<section>P\<section> TBOUND c b"
  using assms
  unfolding htt_def cond_TBOUND_def by simp

lemma htt_intro:
  assumes "<P> c <Q>"
    and   "\<section>P\<section> TBOUND c b"
  shows "<P> c <Q> T[b]"
  using assms unfolding htt_def cond_TBOUND_def by simp

lemma cond_TBOUND_mono: "\<section>P\<section> TBOUND c b \<Longrightarrow> b \<le> b' \<Longrightarrow> \<section>P\<section> TBOUND c b'"
  unfolding cond_TBOUND_def by auto

lemma time_leq_bindy: "time c h \<le> t1 \<Longrightarrow> time (d (the_res c h)) (the_heap c h) \<le> t2 \<Longrightarrow>
              time (c \<bind> d) h \<le> t1+t2"
 by (simp add: time_bind)

lemma cond_TBOUND_bind[cond_TBOUND]: 
  assumes "\<section>P\<section> TBOUND c t1" 
  and "<P> c <Q>"  
  and "(\<And> x h. x = the_res c h \<Longrightarrow> \<section>Q x\<section> TBOUND (d x) t2)"
shows  "\<section>P\<section> TBOUND (c \<bind> d) (t1+t2)"
  unfolding cond_TBOUND_def hoare_triple_def 
  apply auto
  subgoal for h as
    apply(cases "fails (d (the_res c h)) (the_heap c h)")
   apply (simp add: time_bind)
    apply(rule time_leq_bindy)
    subgoal
    using assms  unfolding cond_TBOUND_def hoare_triple_def 
    apply auto
    done
  using assms(3)[of "(the_res c h)" h]
  unfolding cond_TBOUND_def
  using assms(2) 
  unfolding hoare_triple_def Let_def the_res_def the_heap_def
  apply(auto split: option.split)
   apply force+
  done
  done
    
lemma cond_TBOUND_return[cond_TBOUND]: "\<section> P \<section> TBOUND (return x) 1"
  by (simp add: cond_TBOUND_def time_return)

lemma cond_TBOUND_cons:
  assumes "P \<Longrightarrow>\<^sub>A Q"
      and "\<section> Q \<section> TBOUND c b"
    shows "\<section> P \<section> TBOUND c b"
  using assms
  unfolding cond_TBOUND_def
  apply sep_auto
  by (meson entailsD)

method cond_TBOUND= (rule cond_TBOUND_mono, rule cond_TBOUND)



end
