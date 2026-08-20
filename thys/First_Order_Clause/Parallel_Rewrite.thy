theory Parallel_Rewrite
  imports 
    Parallel_Induct 
    Generic_Term_Context
    Ground_Term_Rewrite_System
begin

locale parallel_rewrite =
  term_interpretation where Fun = Fun and is_var = "\<lambda>_. False" +
  smaller_subcontext where size = size\<^sub>c +
  replace_at_subterm where Fun = Fun and is_var = "\<lambda>_. False" +
  ground_term_rewrite_system
  for Fun :: "'f \<Rightarrow> 'e \<Rightarrow> 't list \<Rightarrow> 't" and size\<^sub>c :: "'c \<Rightarrow> nat"
begin

lemma parallel_induct_in_positions [case_names parallel p\<^sub>1_in_t p\<^sub>2_in_t base step]: 
  assumes
    parallel: "p\<^sub>1 \<bottom> p\<^sub>2" and
    p\<^sub>1_in_t: "p\<^sub>1 \<in> positions t" and
    p\<^sub>2_in_t: "p\<^sub>2 \<in> positions t" and
    base: 
      "\<And>p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t f e ts.
        p\<^sub>1 = i # q\<^sub>1 \<Longrightarrow> 
        p\<^sub>2 = j # q\<^sub>2 \<Longrightarrow>
        i \<noteq> j \<Longrightarrow>
        t = Fun f e ts \<Longrightarrow>
        j < length ts \<Longrightarrow>
        i < length ts \<Longrightarrow>
        P p\<^sub>1 p\<^sub>2 t" and
    step: 
      "\<And>p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t f e ts.
        p\<^sub>1 = k # p @ i # q\<^sub>1 \<Longrightarrow>
        p\<^sub>2 = k # p @ j # q\<^sub>2 \<Longrightarrow>
        i \<noteq> j \<Longrightarrow>
        t = Fun f e ts \<Longrightarrow> 
        k < length ts \<Longrightarrow>
        p\<^sub>1 \<in> positions t \<Longrightarrow>
        p\<^sub>2 \<in> positions t \<Longrightarrow>
        P (p @ i # q\<^sub>1) (p @ j # q\<^sub>2) (ts ! k) \<Longrightarrow>
        P p\<^sub>1 p\<^sub>2 t"
    shows "P p\<^sub>1 p\<^sub>2 t"
  using p\<^sub>1_in_t p\<^sub>2_in_t
proof (induction arbitrary: t rule: parallel_induct[OF parallel])
  case base': (1 p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t)

  obtain f e ts where t: "t = Fun f e ts" 
    using term_destruct[of t]
    by blast

  moreover have "i < length ts" 
    using base'(4) t
    unfolding base'(1)
    by simp

  moreover have "j < length ts"
    using base'(5) t
    unfolding base'(2)
    by simp

  ultimately show ?case
    using base' base
    by metis
next
  case step': (2 p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t)

  obtain f e ts where t: "t = Fun f e ts"
    using term_destruct
    by metis

  then have k: "k < length ts"
    using step'(5)
    unfolding step'(1)
    by simp

  show ?case
  proof (rule step[OF step'(1, 2, 3) t k step'(5, 6)])

    let ?p\<^sub>1 = "p @ i # q\<^sub>1"
    let ?p\<^sub>2 = "p @ j # q\<^sub>2" 

    have "?p\<^sub>1 \<in> positions (ts ! k)"  "?p\<^sub>2 \<in> positions (ts ! k)"
      using step'(5, 6)
      unfolding step'(1, 2)
      by (simp_all add: t)

    then show "P ?p\<^sub>1 ?p\<^sub>2 (ts ! k)"
      using step'.IH
      by blast
  qed
qed

lemma parallel_replace_at:
  assumes "p\<^sub>1 \<bottom> p\<^sub>2"  "p\<^sub>1 \<in> positions t" "p\<^sub>2 \<in> positions t"
  shows "t\<lbrakk>p\<^sub>1 := s\<^sub>1\<rbrakk>\<lbrakk>p\<^sub>2 := s\<^sub>2\<rbrakk> = t\<lbrakk>p\<^sub>2 := s\<^sub>2\<rbrakk>\<lbrakk>p\<^sub>1 := s\<^sub>1\<rbrakk>"
proof (induction rule: parallel_induct_in_positions[OF assms])
  case base: (1 p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t f e ts)

  let ?p\<^sub>1 = "i # q\<^sub>1"
  let ?p\<^sub>2 = "j # q\<^sub>2"
  let ?s\<^sub>1 = "(ts ! i)\<lbrakk>q\<^sub>1 := s\<^sub>1\<rbrakk>"
  let ?s\<^sub>2 = "(ts ! j)\<lbrakk>q\<^sub>2 := s\<^sub>2\<rbrakk>"
  let ?ts\<^sub>1 = "ts[i := ?s\<^sub>1]"
  let ?ts\<^sub>2 = "ts[j := ?s\<^sub>2]"

  note i_neq_j = base(3)

  note i = base(6)
  note j = base(5)

  have j': "j < length ?ts\<^sub>1" and i': "i < length ?ts\<^sub>2" 
    using i j
    by simp_all

  have "t\<lbrakk>?p\<^sub>1 := s\<^sub>1\<rbrakk>\<lbrakk>?p\<^sub>2 := s\<^sub>2\<rbrakk> = (Fun f e ?ts\<^sub>1)\<lbrakk>?p\<^sub>2 := s\<^sub>2\<rbrakk>" 
    unfolding base upd_conv_take_nth_drop[OF i]
    by simp

  also have "... = Fun f e (?ts\<^sub>1[j := ?s\<^sub>2])"
    unfolding upd_conv_take_nth_drop[OF j']
    using i_neq_j
    by simp

  also have "... = Fun f e (?ts\<^sub>2[i := ?s\<^sub>1])"
    using list_update_swap[OF i_neq_j]
    by metis

  also have "... = (Fun f e ?ts\<^sub>2)\<lbrakk>?p\<^sub>1 := s\<^sub>1\<rbrakk>"
    unfolding upd_conv_take_nth_drop[OF i'] 
    using i_neq_j
    by simp

  also have "... = t\<lbrakk>?p\<^sub>2 := s\<^sub>2\<rbrakk>\<lbrakk>?p\<^sub>1 := s\<^sub>1\<rbrakk>" 
    unfolding upd_conv_take_nth_drop[OF j] base
    by simp

  finally show ?case
    unfolding base
    by satx
next
  case step: 2

  then show ?case
    by (simp add: nth_append)
qed

lemma parallel_rewrite_in_context:
  assumes 
    parallel: "p\<^sub>1 \<bottom> p\<^sub>2" and
    p\<^sub>1_in_t: "p\<^sub>1 \<in> positions t" and
    p\<^sub>2_in_t: "p\<^sub>2 \<in> positions t" and
    l\<^sub>2: "l\<^sub>2 = t !\<^sub>t p\<^sub>2" and
    l\<^sub>2_r\<^sub>2: "(l\<^sub>2, r\<^sub>2) \<in> R" 
  shows "(t\<lbrakk>p\<^sub>1 := v\<rbrakk>, t\<lbrakk>p\<^sub>1 := v\<rbrakk>\<lbrakk>p\<^sub>2 := r\<^sub>2\<rbrakk>) \<in> rewrite_in_context R" (is "(?t\<^sub>1,?t\<^sub>2) \<in> _")
proof (unfold rewrite_in_context_def mem_Collect_eq, intro exI conjI)
  let ?c = "t\<lbrakk>p\<^sub>1 := v\<rbrakk> !\<^sub>c p\<^sub>2"

  show "(?t\<^sub>1, ?t\<^sub>2) = (?c\<langle>l\<^sub>2\<rangle>, ?c\<langle>r\<^sub>2\<rangle>)"
    unfolding l\<^sub>2 parallel_replace_at[OF parallel p\<^sub>1_in_t p\<^sub>2_in_t] context_at_subterm_at[OF p\<^sub>2_in_t] ..  
qed (rule l\<^sub>2_r\<^sub>2)

end

end
