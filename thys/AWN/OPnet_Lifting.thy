(*  Title:       OPnet_Lifting.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

header "Lifting rules for (open) partial networks"

theory OPnet_Lifting
imports ONode_Lifting OAWN_SOS OPnet
begin

lemma oreachable_par_subnet_induct [consumes, case_names init other local]:
  assumes "(\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) S U"
      and init: "\<And>\<sigma> s t. (\<sigma>, SubnetS s t) \<in> init (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) \<Longrightarrow> P \<sigma> s t"
      and other: "\<And>\<sigma> s t \<sigma>'. \<lbrakk> (\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) S U;
                                U \<sigma> \<sigma>'; P \<sigma> s t \<rbrakk> \<Longrightarrow> P \<sigma>' s t"
      and local: "\<And>\<sigma> s t \<sigma>' s' t' a. \<lbrakk> (\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) S U;
                    ((\<sigma>, SubnetS s t), a, (\<sigma>', SubnetS s' t')) \<in> trans (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2));
                    S \<sigma> \<sigma>' a; P \<sigma> s t \<rbrakk> \<Longrightarrow> P \<sigma>' s' t'"
    shows "P \<sigma> s t"
  using assms(1) proof (induction "(\<sigma>, SubnetS s t)" arbitrary: s t \<sigma>)
    fix s t \<sigma>
    assume "(\<sigma>, SubnetS s t) \<in> init (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))"
    with init show "P \<sigma> s t" .
  next
    fix st a s' t' \<sigma>'
    assume "st \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) S U"
       and tr: "(st, a, (\<sigma>', SubnetS s' t')) \<in> trans (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))"
       and "S (fst st) (fst (\<sigma>', SubnetS s' t')) a"
       and IH: "\<And>s t \<sigma>. st = (\<sigma>, SubnetS s t) \<Longrightarrow> P \<sigma> s t"
    from this(1) obtain s t \<sigma> where "st = (\<sigma>, SubnetS s t)"
                                and "(\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) S U"
      by (metis net_par_oreachable_is_subnet pair_collapse)
    note this(2)
    moreover from tr and `st = (\<sigma>, SubnetS s t)`
      have "((\<sigma>, SubnetS s t), a, (\<sigma>', SubnetS s' t')) \<in> trans (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))" by simp
    moreover from `S (fst st) (fst (\<sigma>', SubnetS s' t')) a` and `st = (\<sigma>, SubnetS s t)`
      have "S \<sigma> \<sigma>' a" by simp
    moreover from IH and `st = (\<sigma>, SubnetS s t)` have "P \<sigma> s t" .
    ultimately show "P \<sigma>' s' t'" by (rule local)
  next
    fix st \<sigma>' s t
    assume "st \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) S U"
       and "U (fst st) \<sigma>'"
       and "snd st = SubnetS s t"
       and IH: "\<And>s t \<sigma>. st = (\<sigma>, SubnetS s t) \<Longrightarrow> P \<sigma> s t"
    from this(1,3) obtain \<sigma> where "st = (\<sigma>, SubnetS s t)"
                              and "(\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) S U"
      by (metis pair_collapse)
    note this(2)
    moreover from `U (fst st) \<sigma>'` and `st = (\<sigma>, SubnetS s t)` have "U \<sigma> \<sigma>'" by simp
    moreover from IH and `st = (\<sigma>, SubnetS s t)` have "P \<sigma> s t" .
    ultimately show "P \<sigma>' s t" by (rule other)
  qed

lemma other_net_tree_ips_par_left:
  assumes "other U (net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)) \<sigma> \<sigma>'"
      and "\<And>\<xi>. U \<xi> \<xi>"
    shows "other U (net_tree_ips p\<^sub>1) \<sigma> \<sigma>'"
  proof -
    from assms(1) obtain ineq: "\<forall>i\<in>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2). \<sigma>' i = \<sigma> i"
                     and outU: "\<forall>j. j\<notin>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2) \<longrightarrow> U (\<sigma> j) (\<sigma>' j)" ..
    show ?thesis
    proof (rule otherI)
      fix i
      assume "i\<in>net_tree_ips p\<^sub>1"
      hence "i\<in>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)" by simp
      with ineq show "\<sigma>' i = \<sigma> i" ..
    next
      fix j
      assume "j\<notin>net_tree_ips p\<^sub>1"
      show "U (\<sigma> j) (\<sigma>' j)"
      proof (cases "j\<in>net_tree_ips p\<^sub>2")
        assume "j\<in>net_tree_ips p\<^sub>2"
        hence "j\<in>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)" by simp
        with ineq have "\<sigma>' j = \<sigma> j" ..
        thus "U (\<sigma> j) (\<sigma>' j)"
          by simp (rule `\<And>\<xi>. U \<xi> \<xi>`)
      next
        assume "j\<notin>net_tree_ips p\<^sub>2"
        with `j\<notin>net_tree_ips p\<^sub>1` have "j\<notin>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)" by simp
        with outU show "U (\<sigma> j) (\<sigma>' j)" by simp
      qed
    qed
  qed

lemma other_net_tree_ips_par_right:
  assumes "other U (net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)) \<sigma> \<sigma>'"
      and "\<And>\<xi>. U \<xi> \<xi>"
    shows "other U (net_tree_ips p\<^sub>2) \<sigma> \<sigma>'"
  proof -
    from assms(1) have "other U (net_tree_ips (p\<^sub>2 \<parallel> p\<^sub>1)) \<sigma> \<sigma>'"
      by (subst net_tree_ips_commute)
    thus ?thesis using `\<And>\<xi>. U \<xi> \<xi>`
      by (rule other_net_tree_ips_par_left)
  qed

lemma ostep_arrive_invariantD [elim]:
  assumes "p \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, U \<rightarrow>) P"
      and "(\<sigma>, s) \<in> oreachable p (otherwith S IPS (oarrivemsg I)) U"
      and "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans p"
      and "oarrivemsg I \<sigma> a"
    shows "P ((\<sigma>, s), a, (\<sigma>', s'))"
  proof -
    from assms(2) have "(\<sigma>, s) \<in> oreachable p (\<lambda>\<sigma> _ a. oarrivemsg I \<sigma> a) U"
      by (rule oreachable_weakenE) auto
    thus "P ((\<sigma>, s), a, (\<sigma>', s'))"
      using assms(3-4) by (rule ostep_invariantD [OF assms(1)])
  qed

lemma opnet_sync_action_subnet_oreachable:
  assumes "(\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))
                                         (\<lambda>\<sigma> _. oarrivemsg I \<sigma>) (other U (net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)))"
          (is "_ \<in> oreachable _ (?S (p\<^sub>1 \<parallel> p\<^sub>2)) (?U (p\<^sub>1 \<parallel> p\<^sub>2))")

      and "\<And>\<xi>. U \<xi> \<xi>"

      and act1: "opnet onp p\<^sub>1 \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U (net_tree_ips p\<^sub>1) \<rightarrow>)
                   globala (\<lambda>(\<sigma>, a, \<sigma>'). castmsg (I \<sigma>) a
                                          \<and> (a = \<tau> \<or> (\<exists>i d. a = i:deliver(d)) \<longrightarrow>
                                                 ((\<forall>i\<in>net_tree_ips p\<^sub>1. U (\<sigma> i) (\<sigma>' i))
                                               \<and> (\<forall>i. i\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' i = \<sigma> i))))"

      and act2: "opnet onp p\<^sub>2 \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U (net_tree_ips p\<^sub>2) \<rightarrow>)
                   globala (\<lambda>(\<sigma>, a, \<sigma>'). castmsg (I \<sigma>) a
                                          \<and> (a = \<tau> \<or> (\<exists>i d. a = i:deliver(d)) \<longrightarrow>
                                                 ((\<forall>i\<in>net_tree_ips p\<^sub>2. U (\<sigma> i) (\<sigma>' i))
                                               \<and> (\<forall>i. i\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' i = \<sigma> i))))"

    shows "(\<sigma>, s) \<in> oreachable (opnet onp p\<^sub>1) (\<lambda>\<sigma> _. oarrivemsg I \<sigma>) (other U (net_tree_ips p\<^sub>1))
           \<and> (\<sigma>, t) \<in> oreachable (opnet onp p\<^sub>2) (\<lambda>\<sigma> _. oarrivemsg I \<sigma>) (other U (net_tree_ips p\<^sub>2))
           \<and> net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}"
  using assms(1)
  proof (induction rule: oreachable_par_subnet_induct)
    case (init \<sigma> s t)
    hence sinit: "(\<sigma>, s) \<in> init (opnet onp p\<^sub>1)"
      and tinit: "(\<sigma>, t) \<in> init (opnet onp p\<^sub>2)"
      and "net_ips s \<inter> net_ips t = {}" by auto
    moreover from sinit have "net_ips s = net_tree_ips p\<^sub>1"
      by (rule opnet_net_ips_net_tree_ips_init)
    moreover from tinit have "net_ips t = net_tree_ips p\<^sub>2"
      by (rule opnet_net_ips_net_tree_ips_init)
    ultimately show ?case by (auto elim: oreachable_init)
  next
    case (other \<sigma> s t \<sigma>')
    hence "other U (net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)) \<sigma> \<sigma>'"
      and IHs: "(\<sigma>, s) \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
      and IHt: "(\<sigma>, t) \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
      and "net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}" by auto

    have "(\<sigma>', s) \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
    proof -
      from `?U (p\<^sub>1 \<parallel> p\<^sub>2) \<sigma> \<sigma>'` and `\<And>\<xi>. U \<xi> \<xi>` have "?U p\<^sub>1 \<sigma> \<sigma>'"
        by (rule other_net_tree_ips_par_left)
      with IHs show ?thesis by - (erule(1) oreachable_other')
    qed

    moreover have "(\<sigma>', t) \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
    proof -
      from `?U (p\<^sub>1 \<parallel> p\<^sub>2) \<sigma> \<sigma>'` and `\<And>\<xi>. U \<xi> \<xi>` have "?U p\<^sub>2 \<sigma> \<sigma>'"
        by (rule other_net_tree_ips_par_right)
      with IHt show ?thesis by - (erule(1) oreachable_other')
    qed

    ultimately show ?case using `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}` by simp
  next
    case (local \<sigma> s t \<sigma>' s' t' a)
    hence stor: "(\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) (?S (p\<^sub>1 \<parallel> p\<^sub>2)) (?U (p\<^sub>1 \<parallel> p\<^sub>2))"
      and tr: "((\<sigma>, SubnetS s t), a, (\<sigma>', SubnetS s' t')) \<in> trans (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))"
      and "oarrivemsg I \<sigma> a"
      and sor: "(\<sigma>, s) \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
      and tor: "(\<sigma>, t) \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
      and "net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}" by auto
    from tr have "((\<sigma>, SubnetS s t), a, (\<sigma>', SubnetS s' t'))
                    \<in> opnet_sos (trans (opnet onp p\<^sub>1)) (trans (opnet onp p\<^sub>2))" by simp
    hence "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)
         \<and> (\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
    proof (cases)
      fix H K m H' K'
      assume "a = (H \<union> H')\<not>(K \<union> K'):arrive(m)"
         and str: "((\<sigma>, s), H\<not>K:arrive(m), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), H'\<not>K':arrive(m), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
      from this(1) and `oarrivemsg I \<sigma> a` have "I \<sigma> m" by simp

      with sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from `I \<sigma> m` tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix R m H K
      assume str: "((\<sigma>, s), R:*cast(m), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), H\<not>K:arrive(m), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"                                    
      from sor str have "I \<sigma> m"
        by - (drule(1) ostep_invariantD [OF act1], simp_all)
      with sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from `I \<sigma> m` tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix R m H K
      assume str: "((\<sigma>, s), H\<not>K:arrive(m), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), R:*cast(m), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"                                    
      from tor ttr have "I \<sigma> m"
        by - (drule(1) ostep_invariantD [OF act2], simp_all)
      with sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from `I \<sigma> m` tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix i i'
      assume str: "((\<sigma>, s), connect(i, i'), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), connect(i, i'), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
      with sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix i i'
      assume str: "((\<sigma>, s), disconnect(i, i'), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), disconnect(i, i'), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
      with sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix i d
      assume "t' = t"
         and str: "((\<sigma>, s), i:deliver(d), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"

      from sor str have "\<forall>j. j\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j"
        by - (drule(1) ostep_invariantD [OF act1], simp_all)
      moreover with `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}`
        have "\<forall>j. j\<in>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j" by auto
      moreover from sor str have "\<forall>j\<in>net_tree_ips p\<^sub>1. U (\<sigma> j) (\<sigma>' j)"
        by - (drule(1) ostep_invariantD [OF act1], simp_all)
      ultimately have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
        using tor `t' = t` by (clarsimp elim!: oreachable_other')
                              (metis otherI `\<And>\<xi>. U \<xi> \<xi>`)+

      moreover from sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis by (rule conjI [rotated])
    next
      fix i d
      assume "s' = s"
         and ttr: "((\<sigma>, t), i:deliver(d), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"

      from tor ttr have "\<forall>j. j\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j"
        by - (drule(1) ostep_invariantD [OF act2], simp_all)
      moreover with `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}`
        have "\<forall>j. j\<in>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j" by auto
      moreover from tor ttr have "\<forall>j\<in>net_tree_ips p\<^sub>2. U (\<sigma> j) (\<sigma>' j)"
        by - (drule(1) ostep_invariantD [OF act2], simp_all)
      ultimately have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
        using sor `s' = s` by (clarsimp elim!: oreachable_other')
                              (metis otherI `\<And>\<xi>. U \<xi> \<xi>`)+

      moreover from tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      assume "t' = t"
         and str: "((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"

      from sor str have "\<forall>j. j\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j"
        by - (drule(1) ostep_invariantD [OF act1], simp_all)
      moreover with `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}`
        have "\<forall>j. j\<in>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j" by auto
      moreover from sor str have "\<forall>j\<in>net_tree_ips p\<^sub>1. U (\<sigma> j) (\<sigma>' j)"
        by - (drule(1) ostep_invariantD [OF act1], simp_all)
      ultimately have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
        using tor `t' = t` by (clarsimp elim!: oreachable_other')
                              (metis otherI `\<And>\<xi>. U \<xi> \<xi>`)+

      moreover from sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis by (rule conjI [rotated])
    next
      assume "s' = s"
         and ttr: "((\<sigma>, t), \<tau>, (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"

      from tor ttr have "\<forall>j. j\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j"
        by - (drule(1) ostep_invariantD [OF act2], simp_all)
      moreover with `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}`
        have "\<forall>j. j\<in>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j" by auto
      moreover from tor ttr have "\<forall>j\<in>net_tree_ips p\<^sub>2. U (\<sigma> j) (\<sigma>' j)"
        by - (drule(1) ostep_invariantD [OF act2], simp_all)
      ultimately have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
        using sor `s' = s` by (clarsimp elim!: oreachable_other')
                              (metis otherI `\<And>\<xi>. U \<xi> \<xi>`)+

      moreover from tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    qed
    with `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}` show ?case by simp
  qed

text {*
  `Splitting' reachability is trivial when there are no assumptions on interleavings, but
  this is useless for showing non-trivial properties, since the interleaving steps can do
  anything at all. This lemma is too weak.
*}

lemma subnet_oreachable_true_true:
  assumes "(\<sigma>, SubnetS s\<^sub>1 s\<^sub>2) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) (\<lambda>_ _ _. True) (\<lambda>_ _. True)"
    shows "(\<sigma>, s\<^sub>1) \<in> oreachable (opnet onp p\<^sub>1) (\<lambda>_ _ _. True) (\<lambda>_ _. True)"
          "(\<sigma>, s\<^sub>2) \<in> oreachable (opnet onp p\<^sub>2) (\<lambda>_ _ _. True) (\<lambda>_ _. True)"
          (is "_ \<in> ?oreachable p\<^sub>2")
  using assms proof -
    from assms have "(\<sigma>, s\<^sub>1) \<in> ?oreachable p\<^sub>1 \<and> (\<sigma>, s\<^sub>2) \<in> ?oreachable p\<^sub>2"
    proof (induction rule: oreachable_par_subnet_induct)
      fix \<sigma> s\<^sub>1 s\<^sub>2
      assume "(\<sigma>, SubnetS s\<^sub>1 s\<^sub>2) \<in> init (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))"
      thus "(\<sigma>, s\<^sub>1) \<in> ?oreachable p\<^sub>1 \<and> (\<sigma>, s\<^sub>2) \<in> ?oreachable p\<^sub>2"
        by (auto dest: oreachable_init)
    next
      case (local \<sigma> s\<^sub>1 s\<^sub>2 \<sigma>' s\<^sub>1' s\<^sub>2' a)
      hence "(\<sigma>, SubnetS s\<^sub>1 s\<^sub>2) \<in> ?oreachable (p\<^sub>1 \<parallel> p\<^sub>2)"
        and sr1: "(\<sigma>, s\<^sub>1) \<in> ?oreachable p\<^sub>1"
        and sr2: "(\<sigma>, s\<^sub>2) \<in> ?oreachable p\<^sub>2"
        and "((\<sigma>, SubnetS s\<^sub>1 s\<^sub>2), a, (\<sigma>', SubnetS s\<^sub>1' s\<^sub>2')) \<in> trans (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))" by auto
      from this(4)
        have "((\<sigma>, SubnetS s\<^sub>1 s\<^sub>2), a, (\<sigma>', SubnetS s\<^sub>1' s\<^sub>2'))
                \<in> opnet_sos (trans (opnet onp p\<^sub>1)) (trans (opnet onp p\<^sub>2))" by simp
      thus "(\<sigma>', s\<^sub>1') \<in> ?oreachable p\<^sub>1 \<and> (\<sigma>', s\<^sub>2') \<in> ?oreachable p\<^sub>2"
      proof cases
        fix R m H K
        assume "a = R:*cast(m)"
           and tr1: "((\<sigma>, s\<^sub>1), R:*cast(m), (\<sigma>', s\<^sub>1')) \<in> trans (opnet onp p\<^sub>1)"
           and tr2: "((\<sigma>, s\<^sub>2), H\<not>K:arrive(m), (\<sigma>', s\<^sub>2')) \<in> trans (opnet onp p\<^sub>2)"
        from sr1 and tr1 and TrueI have "(\<sigma>', s\<^sub>1') \<in> ?oreachable p\<^sub>1"
          by (rule oreachable_local')
        moreover from sr2 and tr2 and TrueI have "(\<sigma>', s\<^sub>2') \<in> ?oreachable p\<^sub>2"
          by (rule oreachable_local')
        ultimately show ?thesis ..
      next
        assume "a = \<tau>"
           and "s\<^sub>2' = s\<^sub>2"
           and tr1: "((\<sigma>, s\<^sub>1), \<tau>, (\<sigma>', s\<^sub>1')) \<in> trans (opnet onp p\<^sub>1)"
        from sr2 and this(2) have "(\<sigma>', s\<^sub>2') \<in> ?oreachable p\<^sub>2" by auto
        moreover have "(\<lambda>_ _. True) \<sigma> \<sigma>'" by (rule TrueI)
        ultimately have "(\<sigma>', s\<^sub>2') \<in> ?oreachable p\<^sub>2"
          by (rule oreachable_other')
        moreover from sr1 and tr1 and TrueI have "(\<sigma>', s\<^sub>1') \<in> ?oreachable p\<^sub>1"
          by (rule oreachable_local')
      qed (insert sr1 sr2, simp_all, (metis (no_types) oreachable_local'
                                                       oreachable_other')+)
    qed auto
    thus "(\<sigma>, s\<^sub>1) \<in> ?oreachable p\<^sub>1"
         "(\<sigma>, s\<^sub>2) \<in> ?oreachable p\<^sub>2" by auto
  qed

text {*
  It may also be tempting to try splitting from the assumption
  @{term "(\<sigma>, SubnetS s\<^sub>1 s\<^sub>2) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) (\<lambda>_ _ _. True) (\<lambda>_ _. False)"},
  where the environment step would be trivially true (since the assumption is false), but the
  lemma cannot be shown when only one side acts, since it must guarantee the assumption for
  the other side.
*}

lemma lift_opnet_sync_action:
  assumes "\<And>\<xi>. U \<xi> \<xi>"
      and act1: "\<And>i R. \<langle>i : onp i : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, a, _). castmsg (I \<sigma>) a)"
      and act2: "\<And>i R. \<langle>i : onp i : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, a, \<sigma>'). (a \<noteq> \<tau> \<and> (\<forall>i d. a \<noteq> i:deliver(d)) \<longrightarrow> S (\<sigma> i) (\<sigma>' i)))"
      and act3: "\<And>i R. \<langle>i : onp i : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, a, \<sigma>'). (a = \<tau> \<or> (\<exists>d. a = i:deliver(d)) \<longrightarrow> U (\<sigma> i) (\<sigma>' i)))"
  shows "opnet onp p \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U (net_tree_ips p) \<rightarrow>)
                       globala (\<lambda>(\<sigma>, a, \<sigma>'). castmsg (I \<sigma>) a
                                              \<and> (a \<noteq> \<tau> \<and> (\<forall>i d. a \<noteq> i:deliver(d)) \<longrightarrow>
                                                     (\<forall>i\<in>net_tree_ips p. S (\<sigma> i) (\<sigma>' i)))
                                              \<and> (a = \<tau> \<or> (\<exists>i d. a = i:deliver(d)) \<longrightarrow>
                                                     ((\<forall>i\<in>net_tree_ips p. U (\<sigma> i) (\<sigma>' i))
                                                   \<and> (\<forall>i. i\<notin>net_tree_ips p \<longrightarrow> \<sigma>' i = \<sigma> i))))"
    (is "opnet onp p \<Turnstile>\<^sub>A (?I, ?U p \<rightarrow>) ?inv (net_tree_ips p)")
  proof (induction p)
    fix i R
    show "opnet onp \<langle>i; R\<rangle> \<Turnstile>\<^sub>A (?I, ?U \<langle>i; R\<rangle> \<rightarrow>) ?inv (net_tree_ips \<langle>i; R\<rangle>)"
    proof (rule ostep_invariantI, simp only: opnet.simps net_tree_ips.simps)
      fix \<sigma> s a \<sigma>' s'
      assume sor: "(\<sigma>, s) \<in> oreachable (\<langle>i : onp i : R\<rangle>\<^sub>o) (\<lambda>\<sigma> _. oarrivemsg I \<sigma>) (other U {i})"
         and str: "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans (\<langle>i : onp i : R\<rangle>\<^sub>o)"
         and oam: "oarrivemsg I \<sigma> a"             
      hence "castmsg (I \<sigma>) a"
        by - (drule(2) ostep_invariantD [OF act1], simp)
      moreover from sor str oam have "a \<noteq> \<tau> \<and> (\<forall>i d. a \<noteq> i:deliver(d)) \<longrightarrow> S (\<sigma> i) (\<sigma>' i)"
        by - (drule(2) ostep_invariantD [OF act2], simp)
      moreover have "a = \<tau> \<or> (\<exists>i d. a = i:deliver(d)) \<longrightarrow> U (\<sigma> i) (\<sigma>' i)"
      proof -
        from sor str oam have "a = \<tau> \<or> (\<exists>d. a = i:deliver(d)) \<longrightarrow> U (\<sigma> i) (\<sigma>' i)"
          by - (drule(2) ostep_invariantD [OF act3], simp)
        moreover from sor str oam have "\<forall>j. j\<noteq>i \<longrightarrow> (\<forall>d. a \<noteq> j:deliver(d))"
          by - (drule(2) ostep_invariantD [OF node_local_deliver], simp)
        ultimately show ?thesis
          by clarsimp metis
      qed
      moreover from sor str oam have "\<forall>j. j\<noteq>i \<longrightarrow> (\<forall>d. a \<noteq> j:deliver(d))"
        by - (drule(2) ostep_invariantD [OF node_local_deliver], simp)
      moreover from sor str oam have "a = \<tau> \<or> (\<exists>i d. a = i:deliver(d)) \<longrightarrow> (\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j)"
        by - (drule(2) ostep_invariantD [OF node_tau_deliver_unchanged], simp)
      ultimately show "?inv {i} ((\<sigma>, s), a, (\<sigma>', s'))" by simp
    qed
  next
    fix p\<^sub>1 p\<^sub>2
    assume inv1: "opnet onp p\<^sub>1 \<Turnstile>\<^sub>A (?I, ?U p\<^sub>1 \<rightarrow>) ?inv (net_tree_ips p\<^sub>1)"
       and inv2: "opnet onp p\<^sub>2 \<Turnstile>\<^sub>A (?I, ?U p\<^sub>2 \<rightarrow>) ?inv (net_tree_ips p\<^sub>2)"
    show "opnet onp (p\<^sub>1 \<parallel> p\<^sub>2) \<Turnstile>\<^sub>A (?I, ?U (p\<^sub>1 \<parallel> p\<^sub>2) \<rightarrow>) ?inv (net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2))"
    proof (rule ostep_invariantI)
      fix \<sigma> st a \<sigma>' st'
      assume "(\<sigma>, st) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) ?I (?U (p\<^sub>1 \<parallel> p\<^sub>2))"
         and "((\<sigma>, st), a, (\<sigma>', st')) \<in> trans (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))"
         and "oarrivemsg I \<sigma> a"
      from this(1) obtain s t
        where "st = SubnetS s t"
          and *: "(\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) ?I (?U (p\<^sub>1 \<parallel> p\<^sub>2))"
        by - (frule net_par_oreachable_is_subnet, metis)

      from this(2) and inv1 and inv2
        obtain sor: "(\<sigma>, s) \<in> oreachable (opnet onp p\<^sub>1) ?I (?U p\<^sub>1)"
           and tor: "(\<sigma>, t) \<in> oreachable (opnet onp p\<^sub>2) ?I (?U p\<^sub>2)"
           and "net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}"
          by - (drule opnet_sync_action_subnet_oreachable [OF _ `\<And>\<xi>. U \<xi> \<xi>`], auto)

      from * and `((\<sigma>, st), a, (\<sigma>', st')) \<in> trans (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))` and `st = SubnetS s t`
        obtain s' t' where "st' = SubnetS s' t'"
                       and "((\<sigma>, SubnetS s t), a, (\<sigma>', SubnetS s' t'))
                              \<in> opnet_sos (trans (opnet onp p\<^sub>1)) (trans (opnet onp p\<^sub>2))"
          by clarsimp (frule opartial_net_preserves_subnets, metis)

      from this(2)
        have"castmsg (I \<sigma>) a
             \<and> (a \<noteq> \<tau> \<and> (\<forall>i d. a \<noteq> i:deliver(d)) \<longrightarrow> (\<forall>i\<in>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2). S (\<sigma> i) (\<sigma>' i)))
             \<and> (a = \<tau> \<or> (\<exists>i d. a = i:deliver(d)) \<longrightarrow> (\<forall>i\<in>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2). U (\<sigma> i) (\<sigma>' i))
                                                  \<and> (\<forall>i. i \<notin> net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2) \<longrightarrow> \<sigma>' i = \<sigma> i))"
      proof cases
        fix R m H K
        assume "a = R:*cast(m)" 
           and str: "((\<sigma>, s), R:*cast(m), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
           and ttr: "((\<sigma>, t), H\<not>K:arrive(m), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
        from sor and str have "I \<sigma> m \<and> (\<forall>i\<in>net_tree_ips p\<^sub>1. S (\<sigma> i) (\<sigma>' i))"
          by (auto dest: ostep_invariantD [OF inv1])
        moreover with tor and ttr have "\<forall>i\<in>net_tree_ips p\<^sub>2. S (\<sigma> i) (\<sigma>' i)"
          by (auto dest: ostep_invariantD [OF inv2])
        ultimately show ?thesis
          using `a = R:*cast(m)` by auto
      next
        fix R m H K
        assume "a = R:*cast(m)" 
           and str: "((\<sigma>, s), H\<not>K:arrive(m), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
           and ttr: "((\<sigma>, t), R:*cast(m), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
        from tor and ttr have "I \<sigma> m \<and> (\<forall>i\<in>net_tree_ips p\<^sub>2. S (\<sigma> i) (\<sigma>' i))"
          by (auto dest: ostep_invariantD [OF inv2])
        moreover with sor and str have "\<forall>i\<in>net_tree_ips p\<^sub>1. S (\<sigma> i) (\<sigma>' i)"
          by (auto dest: ostep_invariantD [OF inv1])
        ultimately show ?thesis
          using `a = R:*cast(m)` by auto
      next
        fix H K m H' K'
        assume "a = (H \<union> H')\<not>(K \<union> K'):arrive(m)"
           and str: "((\<sigma>, s), H\<not>K:arrive(m), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
           and ttr: "((\<sigma>, t), H'\<not>K':arrive(m), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
        from this(1) and `oarrivemsg I \<sigma> a` have "I \<sigma> m" by simp
        with sor and str have "\<forall>i\<in>net_tree_ips p\<^sub>1. S (\<sigma> i) (\<sigma>' i)"
          by (auto dest: ostep_invariantD [OF inv1])
        moreover from tor and ttr and `I \<sigma> m` have "\<forall>i\<in>net_tree_ips p\<^sub>2. S (\<sigma> i) (\<sigma>' i)"
          by (auto dest: ostep_invariantD [OF inv2])
        ultimately show ?thesis
          using `a = (H \<union> H')\<not>(K \<union> K'):arrive(m)` by auto
      next
        fix i d
        assume "a = i:deliver(d)"
           and str: "((\<sigma>, s), i:deliver(d), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
        with sor have "((\<forall>i\<in>net_tree_ips p\<^sub>1. U (\<sigma> i) (\<sigma>' i))
                       \<and> (\<forall>i. i\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' i = \<sigma> i))"
          by (auto dest!: ostep_invariantD [OF inv1])
        with `a = i:deliver(d)` and `\<And>\<xi>. U \<xi> \<xi>` show ?thesis
          by auto
      next
        fix i d
        assume "a = i:deliver(d)"
           and ttr: "((\<sigma>, t), i:deliver(d), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
        with tor have "((\<forall>i\<in>net_tree_ips p\<^sub>2. U (\<sigma> i) (\<sigma>' i))
                       \<and> (\<forall>i. i\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' i = \<sigma> i))"
          by (auto dest!: ostep_invariantD [OF inv2])
        with `a = i:deliver(d)` and `\<And>\<xi>. U \<xi> \<xi>` show ?thesis
          by auto
      next
        assume "a = \<tau>"
           and str: "((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
        with sor have "((\<forall>i\<in>net_tree_ips p\<^sub>1. U (\<sigma> i) (\<sigma>' i))
                       \<and> (\<forall>i. i\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' i = \<sigma> i))"
          by (auto dest!: ostep_invariantD [OF inv1])
        with `a = \<tau>` and `\<And>\<xi>. U \<xi> \<xi>` show ?thesis
          by auto
      next
        assume "a = \<tau>"
           and ttr: "((\<sigma>, t), \<tau>, (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
        with tor have "((\<forall>i\<in>net_tree_ips p\<^sub>2. U (\<sigma> i) (\<sigma>' i))
                       \<and> (\<forall>i. i\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' i = \<sigma> i))"
          by (auto dest!: ostep_invariantD [OF inv2])
        with `a = \<tau>` and `\<And>\<xi>. U \<xi> \<xi>` show ?thesis
          by auto
      next
        fix i i'
        assume "a = connect(i, i')"
           and str: "((\<sigma>, s), connect(i, i'), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
           and ttr: "((\<sigma>, t), connect(i, i'), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
        from sor and str have "\<forall>i\<in>net_tree_ips p\<^sub>1. S (\<sigma> i) (\<sigma>' i)"
          by (auto dest: ostep_invariantD [OF inv1])
        moreover from tor and ttr have "\<forall>i\<in>net_tree_ips p\<^sub>2. S (\<sigma> i) (\<sigma>' i)"
          by (auto dest: ostep_invariantD [OF inv2])
        ultimately show ?thesis
          using `a = connect(i, i')` by auto
      next
        fix i i'
        assume "a = disconnect(i, i')"
           and str: "((\<sigma>, s), disconnect(i, i'), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
           and ttr: "((\<sigma>, t), disconnect(i, i'), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
        from sor and str have "\<forall>i\<in>net_tree_ips p\<^sub>1. S (\<sigma> i) (\<sigma>' i)"
          by (auto dest: ostep_invariantD [OF inv1])
        moreover from tor and ttr have "\<forall>i\<in>net_tree_ips p\<^sub>2. S (\<sigma> i) (\<sigma>' i)"
          by (auto dest: ostep_invariantD [OF inv2])
        ultimately show ?thesis
          using `a = disconnect(i, i')` by auto
      qed
      thus "?inv (net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)) ((\<sigma>, st), a, (\<sigma>', st'))" by simp
    qed
  qed

theorem subnet_oreachable:
  assumes "(\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))
                                (otherwith S (net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)) (oarrivemsg I))
                                (other U (net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)))"
          (is "_ \<in> oreachable _ (?S (p\<^sub>1 \<parallel> p\<^sub>2)) (?U (p\<^sub>1 \<parallel> p\<^sub>2))")

      and "\<And>\<xi>. S \<xi> \<xi>"
      and "\<And>\<xi>. U \<xi> \<xi>"

      and node1: "\<And>i R. \<langle>i : onp i : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, a, _). castmsg (I \<sigma>) a)"
      and node2: "\<And>i R. \<langle>i : onp i : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, a, \<sigma>'). (a \<noteq> \<tau> \<and> (\<forall>i d. a \<noteq> i:deliver(d)) \<longrightarrow> S (\<sigma> i) (\<sigma>' i)))"
      and node3: "\<And>i R. \<langle>i : onp i : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, a, \<sigma>'). (a = \<tau> \<or> (\<exists>d. a = i:deliver(d)) \<longrightarrow> U (\<sigma> i) (\<sigma>' i)))"

    shows "(\<sigma>, s) \<in> oreachable (opnet onp p\<^sub>1)
                               (otherwith S (net_tree_ips p\<^sub>1) (oarrivemsg I))
                               (other U (net_tree_ips p\<^sub>1))
           \<and> (\<sigma>, t) \<in> oreachable (opnet onp p\<^sub>2)
                                  (otherwith S (net_tree_ips p\<^sub>2) (oarrivemsg I))
                                  (other U (net_tree_ips p\<^sub>2))
           \<and> net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}"
  using assms(1) proof (induction rule: oreachable_par_subnet_induct)
    case (init \<sigma> s t)
    hence sinit: "(\<sigma>, s) \<in> init (opnet onp p\<^sub>1)"
      and tinit: "(\<sigma>, t) \<in> init (opnet onp p\<^sub>2)"
      and "net_ips s \<inter> net_ips t = {}" by auto
    moreover from sinit have "net_ips s = net_tree_ips p\<^sub>1"
      by (rule opnet_net_ips_net_tree_ips_init)
    moreover from tinit have "net_ips t = net_tree_ips p\<^sub>2"
      by (rule opnet_net_ips_net_tree_ips_init)
    ultimately show ?case by (auto elim: oreachable_init)
  next
    case (other \<sigma> s t \<sigma>')
    hence "other U (net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2)) \<sigma> \<sigma>'"
      and IHs: "(\<sigma>, s) \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
      and IHt: "(\<sigma>, t) \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
      and "net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}" by auto

    have "(\<sigma>', s) \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
    proof -
      from `?U (p\<^sub>1 \<parallel> p\<^sub>2) \<sigma> \<sigma>'` and `\<And>\<xi>. U \<xi> \<xi>` have "?U p\<^sub>1 \<sigma> \<sigma>'"
        by (rule other_net_tree_ips_par_left)
      with IHs show ?thesis by - (erule(1) oreachable_other')
    qed

    moreover have "(\<sigma>', t) \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
    proof -
      from `?U (p\<^sub>1 \<parallel> p\<^sub>2) \<sigma> \<sigma>'` and `\<And>\<xi>. U \<xi> \<xi>` have "?U p\<^sub>2 \<sigma> \<sigma>'"
        by (rule other_net_tree_ips_par_right)
      with IHt show ?thesis by - (erule(1) oreachable_other')
    qed

    ultimately show ?case using `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}` by simp
  next
    case (local \<sigma> s t \<sigma>' s' t' a)
    hence stor: "(\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) (?S (p\<^sub>1 \<parallel> p\<^sub>2)) (?U (p\<^sub>1 \<parallel> p\<^sub>2))"
      and tr: "((\<sigma>, SubnetS s t), a, (\<sigma>', SubnetS s' t')) \<in> trans (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))"
      and "?S (p\<^sub>1 \<parallel> p\<^sub>2) \<sigma> \<sigma>' a"
      and sor: "(\<sigma>, s) \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
      and tor: "(\<sigma>, t) \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
      and "net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}" by auto

    have act: "\<And>p. opnet onp p \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U (net_tree_ips p) \<rightarrow>)
                 globala (\<lambda>(\<sigma>, a, \<sigma>'). castmsg (I \<sigma>) a
                                        \<and> (a \<noteq> \<tau> \<and> (\<forall>i d. a \<noteq> i:deliver(d)) \<longrightarrow>
                                               (\<forall>i\<in>net_tree_ips p. S (\<sigma> i) (\<sigma>' i)))
                                        \<and> (a = \<tau> \<or> (\<exists>i d. a = i:deliver(d)) \<longrightarrow>
                                               ((\<forall>i\<in>net_tree_ips p. U (\<sigma> i) (\<sigma>' i))
                                             \<and> (\<forall>i. i\<notin>net_tree_ips p \<longrightarrow> \<sigma>' i = \<sigma> i))))"
      by (rule lift_opnet_sync_action [OF assms(3-6)])

    from `?S (p\<^sub>1 \<parallel> p\<^sub>2) \<sigma> \<sigma>' a` have "\<forall>j. j \<notin> net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2) \<longrightarrow> S (\<sigma> j) (\<sigma>' j)"
                                and "oarrivemsg I \<sigma> a"
      by (auto elim!: otherwithE)
    from tr have "((\<sigma>, SubnetS s t), a, (\<sigma>', SubnetS s' t'))
                    \<in> opnet_sos (trans (opnet onp p\<^sub>1)) (trans (opnet onp p\<^sub>2))" by simp
    hence "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)
         \<and> (\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
    proof (cases)
      fix H K m H' K'
      assume "a = (H \<union> H')\<not>(K \<union> K'):arrive(m)"
         and str: "((\<sigma>, s), H\<not>K:arrive(m), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), H'\<not>K':arrive(m), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
      from this(1) and `?S (p\<^sub>1 \<parallel> p\<^sub>2) \<sigma> \<sigma>' a` have "I \<sigma> m" by auto

      with sor str have "\<forall>i\<in>net_tree_ips p\<^sub>1. S (\<sigma> i) (\<sigma>' i)"
        by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
      moreover from `I \<sigma> m` tor ttr have "\<forall>i\<in>net_tree_ips p\<^sub>2. S (\<sigma> i) (\<sigma>' i)"
        by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
      ultimately have "\<forall>i. S (\<sigma> i) (\<sigma>' i)"
        using `\<forall>j. j \<notin> net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2) \<longrightarrow> S (\<sigma> j) (\<sigma>' j)` by auto

      with `I \<sigma> m` sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from `\<forall>i. S (\<sigma> i) (\<sigma>' i)` `I \<sigma> m` tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix R m H K
      assume str: "((\<sigma>, s), R:*cast(m), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), H\<not>K:arrive(m), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"                                    
      from sor str have "I \<sigma> m"
        by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
      with sor str tor ttr have "\<forall>i. S (\<sigma> i) (\<sigma>' i)"
        using `\<forall>j. j \<notin> net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2) \<longrightarrow> S (\<sigma> j) (\<sigma>' j)`
        by (fastforce dest!: ostep_arrive_invariantD [OF act] ostep_arrive_invariantD [OF act])
      with `I \<sigma> m` sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from `\<forall>i. S (\<sigma> i) (\<sigma>' i)` `I \<sigma> m` tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix R m H K
      assume str: "((\<sigma>, s), H\<not>K:arrive(m), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), R:*cast(m), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"                                    
      from tor ttr have "I \<sigma> m"
        by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
      with sor str tor ttr have "\<forall>i. S (\<sigma> i) (\<sigma>' i)"
        using `\<forall>j. j \<notin> net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2) \<longrightarrow> S (\<sigma> j) (\<sigma>' j)`
        by (fastforce dest!: ostep_arrive_invariantD [OF act] ostep_arrive_invariantD [OF act])
      with `I \<sigma> m` sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from `\<forall>i. S (\<sigma> i) (\<sigma>' i)` `I \<sigma> m` tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix i i'
      assume str: "((\<sigma>, s), connect(i, i'), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), connect(i, i'), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
      with sor tor have "\<forall>i. S (\<sigma> i) (\<sigma>' i)"
        using `\<forall>j. j \<notin> net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2) \<longrightarrow> S (\<sigma> j) (\<sigma>' j)`
        by (fastforce dest!: ostep_arrive_invariantD [OF act] ostep_arrive_invariantD [OF act])
      with sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from `\<forall>i. S (\<sigma> i) (\<sigma>' i)` tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix i i'
      assume str: "((\<sigma>, s), disconnect(i, i'), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
         and ttr: "((\<sigma>, t), disconnect(i, i'), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
      with sor tor have "\<forall>i. S (\<sigma> i) (\<sigma>' i)"
        using `\<forall>j. j \<notin> net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2) \<longrightarrow> S (\<sigma> j) (\<sigma>' j)`
        by (fastforce dest!: ostep_arrive_invariantD [OF act] ostep_arrive_invariantD [OF act])
      with sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)
      moreover from `\<forall>i. S (\<sigma> i) (\<sigma>' i)` tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)
      ultimately show ?thesis ..
    next
      fix i d
      assume "t' = t"
         and str: "((\<sigma>, s), i:deliver(d), (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
      from sor str have "\<forall>j. j\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j"
        by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
      hence "\<forall>j. j\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> S (\<sigma> j) (\<sigma>' j)"
         by (auto intro: `\<And>\<xi>. S \<xi> \<xi>`)
      with sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)

      moreover have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
      proof -
        from `\<forall>j. j\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j` and `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}`
          have "\<forall>j. j\<in>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j" by auto
        moreover from sor str have "\<forall>j\<in>net_tree_ips p\<^sub>1. U (\<sigma> j) (\<sigma>' j)"
          by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
        ultimately show ?thesis
          using tor `t' = t` `\<forall>j. j \<notin> net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j`
          by (clarsimp elim!: oreachable_other')
             (metis otherI `\<And>\<xi>. U \<xi> \<xi>`)+
      qed
      ultimately show ?thesis ..
    next
      fix i d
      assume "s' = s"
         and ttr: "((\<sigma>, t), i:deliver(d), (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
      from tor ttr have "\<forall>j. j\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j"
        by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
      hence "\<forall>j. j\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> S (\<sigma> j) (\<sigma>' j)"
         by (auto intro: `\<And>\<xi>. S \<xi> \<xi>`)
      with tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)

      moreover have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
      proof -
        from `\<forall>j. j\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j` and `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}`
          have "\<forall>j. j\<in>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j" by auto
        moreover from tor ttr have "\<forall>j\<in>net_tree_ips p\<^sub>2. U (\<sigma> j) (\<sigma>' j)"
          by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
        ultimately show ?thesis
          using sor `s' = s` `\<forall>j. j \<notin> net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j`
          by (clarsimp elim!: oreachable_other')
             (metis otherI `\<And>\<xi>. U \<xi> \<xi>`)+
      qed
      ultimately show ?thesis by - (rule conjI)
    next
      assume "s' = s"
         and ttr: "((\<sigma>, t), \<tau>, (\<sigma>', t')) \<in> trans (opnet onp p\<^sub>2)"
      from tor ttr have "\<forall>j. j\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j"
        by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
      hence "\<forall>j. j\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> S (\<sigma> j) (\<sigma>' j)"
         by (auto intro: `\<And>\<xi>. S \<xi> \<xi>`)
      with tor ttr
        have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
          by - (erule(1) oreachable_local, auto)

      moreover have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
      proof -
        from `\<forall>j. j\<notin>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j` and `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}`
          have "\<forall>j. j\<in>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j" by auto
        moreover from tor ttr have "\<forall>j\<in>net_tree_ips p\<^sub>2. U (\<sigma> j) (\<sigma>' j)"
          by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
        ultimately show ?thesis
          using sor `s' = s` `\<forall>j. j \<notin> net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j`
          by (clarsimp elim!: oreachable_other')
             (metis otherI `\<And>\<xi>. U \<xi> \<xi>`)+
      qed
      ultimately show ?thesis by - (rule conjI)
    next
      assume "t' = t"
         and str: "((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> trans (opnet onp p\<^sub>1)"
      from sor str have "\<forall>j. j\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j"
        by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
      hence "\<forall>j. j\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> S (\<sigma> j) (\<sigma>' j)"
         by (auto intro: `\<And>\<xi>. S \<xi> \<xi>`)
      with sor str
        have "(\<sigma>', s') \<in> oreachable (opnet onp p\<^sub>1) (?S p\<^sub>1) (?U p\<^sub>1)"
          by - (erule(1) oreachable_local, auto)

      moreover have "(\<sigma>', t') \<in> oreachable (opnet onp p\<^sub>2) (?S p\<^sub>2) (?U p\<^sub>2)"
      proof -
        from `\<forall>j. j\<notin>net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j` and `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}`
          have "\<forall>j. j\<in>net_tree_ips p\<^sub>2 \<longrightarrow> \<sigma>' j = \<sigma> j" by auto
        moreover from sor str have "\<forall>j\<in>net_tree_ips p\<^sub>1. U (\<sigma> j) (\<sigma>' j)"
          by - (drule(1) ostep_arrive_invariantD [OF act], simp_all)
        ultimately show ?thesis
          using tor `t' = t` `\<forall>j. j \<notin> net_tree_ips p\<^sub>1 \<longrightarrow> \<sigma>' j = \<sigma> j`
          by (clarsimp elim!: oreachable_other')
             (metis otherI `\<And>\<xi>. U \<xi> \<xi>`)+
      qed
      ultimately show ?thesis ..
    qed
    with `net_tree_ips p\<^sub>1 \<inter> net_tree_ips p\<^sub>2 = {}` show ?case by simp
  qed

lemmas subnet_oreachable1 [dest] = subnet_oreachable [THEN conjunct1, rotated 1]
lemmas subnet_oreachable2 [dest] = subnet_oreachable [THEN conjunct2, THEN conjunct1, rotated 1]
lemmas subnet_oreachable_disjoint [dest] = subnet_oreachable
                                                    [THEN conjunct2, THEN conjunct2, rotated 1]

corollary pnet_lift:
  assumes "\<And>ii R\<^sub>i. \<langle>ii : onp ii : R\<^sub>i\<rangle>\<^sub>o
              \<Turnstile> (otherwith S {ii} (oarrivemsg I), other U {ii} \<rightarrow>) global (P ii)"

      and "\<And>\<xi>. S \<xi> \<xi>"
      and "\<And>\<xi>. U \<xi> \<xi>"

      and node1: "\<And>i R. \<langle>i : onp i : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, a, _). castmsg (I \<sigma>) a)"
      and node2: "\<And>i R. \<langle>i : onp i : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, a, \<sigma>'). (a \<noteq> \<tau> \<and> (\<forall>i d. a \<noteq> i:deliver(d)) \<longrightarrow> S (\<sigma> i) (\<sigma>' i)))"
      and node3: "\<And>i R. \<langle>i : onp i : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg I \<sigma>, other U {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, a, \<sigma>'). (a = \<tau> \<or> (\<exists>d. a = i:deliver(d)) \<longrightarrow> U (\<sigma> i) (\<sigma>' i)))"

    shows "opnet onp p \<Turnstile> (otherwith S (net_tree_ips p) (oarrivemsg I),
                       other U (net_tree_ips p) \<rightarrow>) global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips p. P i \<sigma>)"
      (is "_ \<Turnstile> (?owS p, ?U p \<rightarrow>) _")
  proof (induction p)
    fix ii R\<^sub>i
    from assms(1) show "opnet onp \<langle>ii; R\<^sub>i\<rangle> \<Turnstile> (?owS \<langle>ii; R\<^sub>i\<rangle>, ?U \<langle>ii; R\<^sub>i\<rangle> \<rightarrow>)
                                         global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips \<langle>ii; R\<^sub>i\<rangle>. P i \<sigma>)" by auto
  next
    fix p\<^sub>1 p\<^sub>2
    assume ih1: "opnet onp p\<^sub>1 \<Turnstile> (?owS p\<^sub>1, ?U p\<^sub>1 \<rightarrow>) global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips p\<^sub>1. P i \<sigma>)"
       and ih2: "opnet onp p\<^sub>2 \<Turnstile> (?owS p\<^sub>2, ?U p\<^sub>2 \<rightarrow>) global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips p\<^sub>2. P i \<sigma>)"
    show "opnet onp (p\<^sub>1 \<parallel> p\<^sub>2) \<Turnstile> (?owS (p\<^sub>1 \<parallel> p\<^sub>2), ?U (p\<^sub>1 \<parallel> p\<^sub>2) \<rightarrow>)
                             global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2). P i \<sigma>)"
    unfolding oinvariant_def
    proof
      fix pq
      assume "pq \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2)) (?owS (p\<^sub>1 \<parallel> p\<^sub>2)) (?U (p\<^sub>1 \<parallel> p\<^sub>2))"
      moreover then obtain \<sigma> s t where "pq = (\<sigma>, SubnetS s t)"
        by (metis net_par_oreachable_is_subnet surjective_pairing)
      ultimately have "(\<sigma>, SubnetS s t) \<in> oreachable (opnet onp (p\<^sub>1 \<parallel> p\<^sub>2))
                                               (?owS (p\<^sub>1 \<parallel> p\<^sub>2)) (?U (p\<^sub>1 \<parallel> p\<^sub>2))" by simp
      then obtain sor: "(\<sigma>, s) \<in> oreachable (opnet onp p\<^sub>1) (?owS p\<^sub>1) (?U p\<^sub>1)"
              and tor: "(\<sigma>, t) \<in> oreachable (opnet onp p\<^sub>2) (?owS p\<^sub>2) (?U p\<^sub>2)"
        by - (drule subnet_oreachable [OF _ _ _ node1 node2 node3], auto intro: assms(2-3))
      from sor have "\<forall>i\<in>net_tree_ips p\<^sub>1. P i \<sigma>"
        by (auto dest: oinvariantD [OF ih1])
      moreover from tor have "\<forall>i\<in>net_tree_ips p\<^sub>2. P i \<sigma>"
        by (auto dest: oinvariantD [OF ih2])
      ultimately have "\<forall>i\<in>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2). P i \<sigma>" by auto
      with `pq = (\<sigma>, SubnetS s t)` show "global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips (p\<^sub>1 \<parallel> p\<^sub>2). P i \<sigma>) pq" by simp
    qed
  qed

end
