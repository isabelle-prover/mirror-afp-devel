theory IsaFoR_Ground_Term
  imports 
    "Regular_Tree_Relations.Ground_Terms"
    Parallel_Induct
begin

type_synonym 'f ground_term = "'f gterm"

no_notation Term_Context.position_par (infixl \<open>\<bottom>\<close> 67)

(* TODO: Generalize consts for abstract contexts *)
abbreviation positions\<^sub>G where
  "positions\<^sub>G \<equiv> gposs"

notation gsubt_at (infixl \<open>!\<^sub>t\<^sub>G\<close> 64)

lemma parallel_induct_first_in_positions\<^sub>G [case_names parallel p\<^sub>1_in_t base step]: 
  assumes
    parallel: "p\<^sub>1 \<bottom> p\<^sub>2" and
    p\<^sub>1_in_t: "p\<^sub>1 \<in> positions\<^sub>G t" and
    base: 
      "\<And>p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t f ts.
        p\<^sub>1 = i # q\<^sub>1 \<Longrightarrow> 
        p\<^sub>2 = j # q\<^sub>2 \<Longrightarrow>
        i \<noteq> j \<Longrightarrow>
        t = GFun f ts \<Longrightarrow>
        i < length ts \<Longrightarrow> P p\<^sub>1 p\<^sub>2 t" and
    step: 
      "\<And>p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t f ts.
        p\<^sub>1 = k # p @ i # q\<^sub>1 \<Longrightarrow>
        p\<^sub>2 = k # p @ j # q\<^sub>2 \<Longrightarrow>
        i \<noteq> j \<Longrightarrow>
        t = GFun f ts \<Longrightarrow> 
        k < length ts \<Longrightarrow>
        p\<^sub>1 \<in> positions\<^sub>G t \<Longrightarrow>
        P (p @ i # q\<^sub>1) (p @ j # q\<^sub>2) (ts ! k) \<Longrightarrow>
        P p\<^sub>1 p\<^sub>2 t"
    shows "P p\<^sub>1 p\<^sub>2 t"
  using p\<^sub>1_in_t
proof (induction arbitrary: t rule: parallel_induct[OF parallel])
  case base': (1 p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t)

  then obtain f ts where "t = GFun f ts" "i < length ts"
    by (cases t, auto)

  then show ?case
    using base' base
    by metis
next
  case step': (2 p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t)

  then obtain f ts where t: "t = GFun f ts" and k: "k < length ts" 
    by (cases t, auto)

  show ?case
  proof (rule step[OF step'(1, 2, 3) t k step'(5)])

    let ?p\<^sub>1 = "p @ i # q\<^sub>1"
    let ?p\<^sub>2 = "p @ j # q\<^sub>2" 

    from step' have "?p\<^sub>1 \<in> positions\<^sub>G (ts ! k)"
      unfolding t
      by simp

    then show "P ?p\<^sub>1 ?p\<^sub>2 (ts ! k)"
      using step'.IH
      by blast
  qed
qed

lemma parallel_induct_second_in_positions\<^sub>G [case_names base step]: 
  assumes
    parallel: "p\<^sub>1 \<bottom> p\<^sub>2" and
    p\<^sub>2_in_t: "p\<^sub>2 \<in> positions\<^sub>G t" and
    base: 
      "\<And>p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t f ts.
        p\<^sub>1 = i # q\<^sub>1 \<Longrightarrow> 
        p\<^sub>2 = j # q\<^sub>2 \<Longrightarrow>
        i \<noteq> j \<Longrightarrow>
        t = GFun f ts \<Longrightarrow>
        j < length ts \<Longrightarrow> P p\<^sub>1 p\<^sub>2 t" and
    step: 
      "\<And>p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t f ts.
        p\<^sub>1 = k # p @ i # q\<^sub>1 \<Longrightarrow>
        p\<^sub>2 = k # p @ j # q\<^sub>2 \<Longrightarrow>
        i \<noteq> j \<Longrightarrow>
        t = GFun f ts \<Longrightarrow> 
        k < length ts \<Longrightarrow>
        p\<^sub>2 \<in> positions\<^sub>G t \<Longrightarrow>
        P (p @ i # q\<^sub>1) (p @ j # q\<^sub>2) (ts ! k) \<Longrightarrow>
        P p\<^sub>1 p\<^sub>2 t"
    shows "P p\<^sub>1 p\<^sub>2 t"
  using p\<^sub>2_in_t
proof (induction arbitrary: t rule: parallel_induct[OF parallel])
  case base': (1 p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t)

  then obtain f ts where "t = GFun f ts" "j < length ts"
    by (cases t, auto)

  then show ?case
    using base' base
    by metis
next
  case step': (2 p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t)

  then obtain f ts where t: "t = GFun f ts" and k: "k < length ts" 
    by (cases t, auto)

  show ?case
  proof (rule step[OF step'(1, 2, 3) t k step'(5)])

    let ?p\<^sub>1 = "p @ i # q\<^sub>1"
    let ?p\<^sub>2 = "p @ j # q\<^sub>2" 

    from step' have "?p\<^sub>2 \<in> positions\<^sub>G (ts ! k)"
      unfolding t
      by simp

    then show "P ?p\<^sub>1 ?p\<^sub>2 (ts ! k)"
      using step'.IH
      by blast
  qed
qed

lemma parallel_induct_in_positions\<^sub>G [case_names parallel p\<^sub>1_in_t p\<^sub>2_in_t base step]: 
  assumes
    parallel: "p\<^sub>1 \<bottom> p\<^sub>2" and
    p\<^sub>1_in_t: "p\<^sub>1 \<in> positions\<^sub>G t" and
    p\<^sub>2_in_t: "p\<^sub>2 \<in> positions\<^sub>G t" and
    base: 
      "\<And>p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t f ts.
        p\<^sub>1 = i # q\<^sub>1 \<Longrightarrow> 
        p\<^sub>2 = j # q\<^sub>2 \<Longrightarrow>
        i \<noteq> j \<Longrightarrow>
        t = GFun f ts \<Longrightarrow>
        j < length ts \<Longrightarrow>
        i < length ts \<Longrightarrow>
        P p\<^sub>1 p\<^sub>2 t" and
    step: 
      "\<And>p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t f ts.
        p\<^sub>1 = k # p @ i # q\<^sub>1 \<Longrightarrow>
        p\<^sub>2 = k # p @ j # q\<^sub>2 \<Longrightarrow>
        i \<noteq> j \<Longrightarrow>
        t = GFun f ts \<Longrightarrow> 
        k < length ts \<Longrightarrow>
        p\<^sub>1 \<in> positions\<^sub>G t \<Longrightarrow>
        p\<^sub>2 \<in> positions\<^sub>G t \<Longrightarrow>
        P (p @ i # q\<^sub>1) (p @ j # q\<^sub>2) (ts ! k) \<Longrightarrow>
        P p\<^sub>1 p\<^sub>2 t"
    shows "P p\<^sub>1 p\<^sub>2 t"
  using p\<^sub>1_in_t p\<^sub>2_in_t
proof (induction arbitrary: t rule: parallel_induct[OF parallel ])
  case base': (1 p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t)

  then obtain f ts where "t = GFun f ts" "j < length ts" "i < length ts"
    by (cases t, auto)

  then show ?case
    using base' base
    by metis
next
  case step': (2 p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t)

  then obtain f ts where t: "t = GFun f ts" and k: "k < length ts" 
    by (cases t, auto)

  show ?case
  proof (rule step[OF step'(1, 2, 3) t k step'(5, 6)])

    let ?p\<^sub>1 = "p @ i # q\<^sub>1"
    let ?p\<^sub>2 = "p @ j # q\<^sub>2" 

    from step' have "?p\<^sub>1 \<in> positions\<^sub>G (ts ! k)" "?p\<^sub>2 \<in> positions\<^sub>G (ts ! k)"
      unfolding t
      by simp_all

    then show "P ?p\<^sub>1 ?p\<^sub>2 (ts ! k)"
      using step'.IH
      by blast
  qed
qed

end
