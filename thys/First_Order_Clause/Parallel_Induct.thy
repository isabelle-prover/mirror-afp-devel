theory Parallel_Induct
  imports First_Order_Terms.Position
begin

lemma parallel_induct [case_names parallel base step]: 
  assumes
    parallel: "p\<^sub>1 \<bottom> p\<^sub>2" and
    base: "\<And>p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2. p\<^sub>1 = i # q\<^sub>1 \<Longrightarrow> p\<^sub>2 = j # q\<^sub>2 \<Longrightarrow> i \<noteq> j \<Longrightarrow> P p\<^sub>1 p\<^sub>2" and
    step: 
      "\<And>p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2.
        p\<^sub>1 = k # p @ i # q\<^sub>1 \<Longrightarrow>
        p\<^sub>2 = k # p @ j # q\<^sub>2 \<Longrightarrow>
        i \<noteq> j \<Longrightarrow>
        P (p @ i # q\<^sub>1) (p @ j # q\<^sub>2) \<Longrightarrow>
        P p\<^sub>1 p\<^sub>2"
    shows "P p\<^sub>1 p\<^sub>2"
proof -

  from parallel_remove_prefix[OF parallel]
  obtain p i j q\<^sub>1 q\<^sub>2 where 
    p\<^sub>1: "p\<^sub>1 = p @ i # q\<^sub>1" and 
    p\<^sub>2: "p\<^sub>2 = p @ j # q\<^sub>2" and
    i_neq_j: "i \<noteq> j" 
    by blast

  show ?thesis unfolding p\<^sub>1 p\<^sub>2
    using base step i_neq_j
    by (induction p) auto
qed

end
