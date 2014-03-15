(*  Title:       OClosed_Transfer.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

header "Transfer open results onto closed models"

theory OClosed_Transfer
imports Closed OClosed_Lifting
begin

locale openproc =
  fixes np  :: "ip \<Rightarrow> ('s, ('m::msg) seq_action) automaton"
    and onp :: "ip \<Rightarrow> ((ip \<Rightarrow> 'g) \<times> 'l, 'm seq_action) automaton"
    and sr  :: "'s \<Rightarrow> ('g \<times> 'l)"
  assumes  init: "{ (\<sigma>, \<zeta>) |\<sigma> \<zeta> s. s \<in> init (np i)
                             \<and> (\<sigma> i, \<zeta>) = sr s
                             \<and> (\<forall>j. j\<noteq>i \<longrightarrow> \<sigma> j \<in> (fst o sr) ` init (np j)) } \<subseteq> init (onp i)"
      and init_notempty: "\<forall>j. init (np j) \<noteq> {}"
      and trans: "\<And>s a s' \<sigma> \<sigma>'. \<lbrakk> \<sigma> i = fst (sr s);
                                  \<sigma>' i = fst (sr s');
                                  (s, a, s') \<in> trans (np i) \<rbrakk>
                   \<Longrightarrow> ((\<sigma>, snd (sr s)), a, (\<sigma>', snd (sr s'))) \<in> trans (onp i)"
begin

lemma init_pnet_p_NodeS:
  assumes "NodeS i s R \<in> init (pnet np p)"
    shows "p = \<langle>i; R\<rangle>"
  using assms by (cases p) (auto simp add: node_comps)

lemma init_pnet_p_SubnetS:
  assumes "SubnetS s1 s2 \<in> init (pnet np p)"
  obtains p1 p2 where "p = (p1 \<parallel> p2)"
                  and "s1 \<in> init (pnet np p1)"
                  and "s2 \<in> init (pnet np p2)"
  using assms by (cases p) (auto simp add: node_comps)

lemma init_pnet_fst_sr_netgmap:
  assumes "s \<in> init (pnet np p)"
      and "i \<in> net_ips s"
      and "wf_net_tree p"
    shows "the (fst (netgmap sr s) i) \<in> (fst \<circ> sr) ` init (np i)"
  using assms proof (induction s arbitrary: p)
    fix ii s R\<^sub>i p
    assume "NodeS ii s R\<^sub>i \<in> init (pnet np p)"
       and "i \<in> net_ips (NodeS ii s R\<^sub>i)"
       and "wf_net_tree p"
    note this(1)
    moreover then have "p = \<langle>ii; R\<^sub>i\<rangle>"
      by (rule init_pnet_p_NodeS)
    ultimately have "s \<in> init (np ii)"
      by (clarsimp simp: node_comps)
    with `i \<in> net_ips (NodeS ii s R\<^sub>i)`
      show "the (fst (netgmap sr (NodeS ii s R\<^sub>i)) i) \<in> (fst \<circ> sr) ` init (np i)"
        by clarsimp
  next
    fix s1 s2 p
    assume IH1: "\<And>p. s1 \<in> init (pnet np p)
                  \<Longrightarrow> i \<in> net_ips s1
                  \<Longrightarrow> wf_net_tree p
                  \<Longrightarrow> the (fst (netgmap sr s1) i) \<in> (fst \<circ> sr) ` init (np i)"
       and IH2: "\<And>p. s2 \<in> init (pnet np p)
                  \<Longrightarrow> i \<in> net_ips s2
                  \<Longrightarrow> wf_net_tree p
                  \<Longrightarrow> the (fst (netgmap sr s2) i) \<in> (fst \<circ> sr) ` init (np i)"
       and "SubnetS s1 s2 \<in> init (pnet np p)"
       and "i \<in> net_ips (SubnetS s1 s2)"
       and "wf_net_tree p"
    from this(3) obtain p1 p2 where "p = (p1 \<parallel> p2)"
                                and "s1 \<in> init (pnet np p1)"
                                and "s2 \<in> init (pnet np p2)"
      by (rule init_pnet_p_SubnetS)
    from this(1) and `wf_net_tree p` have "wf_net_tree p1"
                                      and "wf_net_tree p2"
                                      and "net_tree_ips p1 \<inter> net_tree_ips p2 = {}"
      by auto
    from `i \<in> net_ips (SubnetS s1 s2)` have "i \<in> net_ips s1 \<or> i \<in> net_ips s2"
      by simp
    thus "the (fst (netgmap sr (SubnetS s1 s2)) i) \<in> (fst \<circ> sr) ` init (np i)"
    proof
      assume "i \<in> net_ips s1"
      hence "i \<notin> net_ips s2"
      proof -
        from `s1 \<in> init (pnet np p1)` and `i \<in> net_ips s1` have "i\<in>net_tree_ips p1" ..
        with `net_tree_ips p1 \<inter> net_tree_ips p2 = {}` have "i\<notin>net_tree_ips p2" by auto
        with `s2 \<in> init (pnet np p2)` show ?thesis ..
      qed
      moreover from `s1 \<in> init (pnet np p1)`  `i \<in> net_ips s1` and `wf_net_tree p1`
        have "the (fst (netgmap sr s1) i) \<in> (fst \<circ> sr) ` init (np i)"
          by (rule IH1)
      ultimately show ?thesis by simp
    next
      assume "i \<in> net_ips s2"
      moreover with `s2 \<in> init (pnet np p2)` have "the (fst (netgmap sr s2) i) \<in> (fst \<circ> sr) ` init (np i)"
        using `wf_net_tree p2` by (rule IH2)
      moreover from `s2 \<in> init (pnet np p2)` and `i \<in> net_ips s2` have "i\<in>net_tree_ips p2" ..
      ultimately show ?thesis by simp
    qed
  qed

lemma init_lifted:
  assumes "wf_net_tree p"                                                          
  shows "{ (\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np p)
                               \<and> (\<forall>i. if i\<in>net_tree_ips p then \<sigma> i = the (fst (netgmap sr s) i)
                                      else \<sigma> i \<in> (fst o sr) ` init (np i)) } \<subseteq> init (opnet onp p)"
  using assms proof (induction p)
    fix i R
    assume "wf_net_tree \<langle>i; R\<rangle>"
    show "{(\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np \<langle>i; R\<rangle>)
            \<and> (\<forall>j. if j \<in> net_tree_ips \<langle>i; R\<rangle> then \<sigma> j = the (fst (netgmap sr s) j)
                   else \<sigma> j \<in> (fst \<circ> sr) ` init (np j))} \<subseteq> init (opnet onp \<langle>i; R\<rangle>)"
      by (clarsimp simp add: node_comps onode_comps)
         (rule set_mp [OF init], auto)
  next
    fix p1 p2
    assume IH1: "wf_net_tree p1
                \<Longrightarrow> {(\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np p1)
                      \<and> (\<forall>i. if i \<in> net_tree_ips p1 then \<sigma> i = the (fst (netgmap sr s) i)
                             else \<sigma> i \<in> (fst \<circ> sr) ` init (np i))} \<subseteq> init (opnet onp p1)"
                (is "_ \<Longrightarrow> ?S1 \<subseteq> _")
       and IH2: "wf_net_tree p2
                 \<Longrightarrow> {(\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np p2)
                       \<and> (\<forall>i. if i \<in> net_tree_ips p2 then \<sigma> i = the (fst (netgmap sr s) i)
                              else \<sigma> i \<in> (fst \<circ> sr) ` init (np i))} \<subseteq> init (opnet onp p2)"
                (is "_ \<Longrightarrow> ?S2 \<subseteq> _")
        and "wf_net_tree (p1 \<parallel> p2)"
    from this(3) have "wf_net_tree p1"
                  and "wf_net_tree p2"
                  and "net_tree_ips p1 \<inter> net_tree_ips p2 = {}" by auto
    show "{(\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np (p1 \<parallel> p2))
            \<and> (\<forall>i. if i \<in> net_tree_ips (p1 \<parallel> p2) then \<sigma> i = the (fst (netgmap sr s) i)
                   else \<sigma> i \<in> (fst \<circ> sr) ` init (np i))} \<subseteq> init (opnet onp (p1 \<parallel> p2))"
    proof (rule, clarsimp simp only: split_paired_all pnet.simps automaton.simps)
      fix \<sigma> s1 s2
      assume \<sigma>_desc: "\<forall>i. if i \<in> net_tree_ips (p1 \<parallel> p2)
                          then \<sigma> i = the (fst (netgmap sr (SubnetS s1 s2)) i)
                          else \<sigma> i \<in> (fst \<circ> sr) ` init (np i)"
         and "s1 \<in> init (pnet np p1)"
         and "s2 \<in> init (pnet np p2)"
      from this(2-3) have "net_ips s1 = net_tree_ips p1"
                      and "net_ips s2 = net_tree_ips p2" by auto
      have "(\<sigma>, snd (netgmap sr s1)) \<in> ?S1"
      proof -
        { fix i
          assume "i \<in> net_tree_ips p1"
          with `net_tree_ips p1 \<inter> net_tree_ips p2 = {}` have "i \<notin> net_tree_ips p2" by auto
          with `s2 \<in> init (pnet np p2)` have "i \<notin> net_ips s2" ..
          hence "the ((fst (netgmap sr s1) ++ fst (netgmap sr s2)) i) = the (fst (netgmap sr s1) i)"
            by simp
        }
        moreover
        { fix i
          assume "i \<notin> net_tree_ips p1"
          have "\<sigma> i \<in> (fst \<circ> sr) ` init (np i)"
          proof (cases "i \<in> net_tree_ips p2")
            assume "i \<notin> net_tree_ips p2"
            with `i \<notin> net_tree_ips p1` and \<sigma>_desc show ?thesis
              by simp
          next
            assume "i \<in> net_tree_ips p2"
            with `s2 \<in> init (pnet np p2)` have "i \<in> net_ips s2" ..
            with `s2 \<in> init (pnet np p2)` have "the (fst (netgmap sr s2) i) \<in> (fst \<circ> sr) ` init (np i)"
              using `wf_net_tree p2` by (rule init_pnet_fst_sr_netgmap)
            with `i\<in>net_tree_ips p2` and `i\<in>net_ips s2` show ?thesis
              using \<sigma>_desc by simp
          qed
        }
        ultimately show ?thesis
          using `s1 \<in> init (pnet np p1)` and \<sigma>_desc by auto
      qed
      hence "(\<sigma>, snd (netgmap sr s1)) \<in> init (opnet onp p1)"
        by (rule set_mp [OF IH1 [OF `wf_net_tree p1`]])

      have "(\<sigma>, snd (netgmap sr s2)) \<in> ?S2"
      proof -
        { fix i
          assume "i \<in> net_tree_ips p2"
          with `s2 \<in> init (pnet np p2)` have "i \<in> net_ips s2" ..
          hence "the ((fst (netgmap sr s1) ++ fst (netgmap sr s2)) i) = the (fst (netgmap sr s2) i)"
            by simp
        }
        moreover
        { fix i
          assume "i \<notin> net_tree_ips p2"
          have "\<sigma> i \<in> (fst \<circ> sr) ` init (np i)"
          proof (cases "i \<in> net_tree_ips p1")
            assume "i \<notin> net_tree_ips p1"
            with `i \<notin> net_tree_ips p2` and \<sigma>_desc show ?thesis
              by simp
          next
            assume "i \<in> net_tree_ips p1"
            with `s1 \<in> init (pnet np p1)` have "i \<in> net_ips s1" ..
            with `s1 \<in> init (pnet np p1)` have "the (fst (netgmap sr s1) i) \<in> (fst \<circ> sr) ` init (np i)"
              using `wf_net_tree p1` by (rule init_pnet_fst_sr_netgmap)
            moreover from `s2 \<in> init (pnet np p2)` and `i \<notin> net_tree_ips p2` have "i\<notin>net_ips s2" ..
            ultimately show ?thesis
              using `i\<in>net_tree_ips p1` `i\<in>net_ips s1` and `i\<notin>net_tree_ips p2` \<sigma>_desc by simp
          qed
        }
        ultimately show ?thesis
          using `s2 \<in> init (pnet np p2)` and \<sigma>_desc by auto
      qed
      hence "(\<sigma>, snd (netgmap sr s2)) \<in> init (opnet onp p2)"
        by (rule set_mp [OF IH2 [OF `wf_net_tree p2`]])

      with `(\<sigma>, snd (netgmap sr s1)) \<in> init (opnet onp p1)`
        show "(\<sigma>, snd (netgmap sr (SubnetS s1 s2))) \<in> init (opnet onp (p1 \<parallel> p2))"
        using `net_tree_ips p1 \<inter> net_tree_ips p2 = {}`
              `net_ips s1 = net_tree_ips p1`
              `net_ips s2 = net_tree_ips p2` by simp
    qed
  qed

lemma init_pnet_opnet [elim]:
  assumes "wf_net_tree p"
      and "s \<in> init (pnet np p)"
    shows "netgmap sr s \<in> netmask (net_tree_ips p) ` init (opnet onp p)"
  proof -
    from `wf_net_tree p`
      have "{ (\<sigma>, snd (netgmap sr s)) |\<sigma> s. s \<in> init (pnet np p)
                              \<and> (\<forall>i. if i\<in>net_tree_ips p then \<sigma> i = the (fst (netgmap sr s) i)
                                     else \<sigma> i \<in> (fst o sr) ` init (np i)) } \<subseteq> init (opnet onp p)"
        (is "?S \<subseteq> _")
      by (rule init_lifted)
    hence "netmask (net_tree_ips p) ` ?S \<subseteq> netmask (net_tree_ips p) ` init (opnet onp p)"
      by (rule image_mono)
    moreover have "netgmap sr s \<in> netmask (net_tree_ips p) ` ?S"
    proof -
      { fix i
        from init_notempty have "\<exists>s. s \<in> (fst \<circ> sr) ` init (np i)" by auto
        hence "(SOME x. x \<in> (fst \<circ> sr) ` init (np i)) \<in> (fst \<circ> sr) ` init (np i)" ..
      }
      with `s \<in> init (pnet np p)` and init_notempty
        have "(\<lambda>i. if i \<in> net_tree_ips p
                   then the (fst (netgmap sr s) i)
                   else SOME x. x \<in> (fst \<circ> sr) ` init (np i), snd (netgmap sr s)) \<in> ?S"
          (is "?s \<in> ?S") by auto
      moreover have "netgmap sr s = netmask (net_tree_ips p) ?s"
      proof (intro prod_eqI ext)
        fix i
        show "fst (netgmap sr s) i = fst (netmask (net_tree_ips p) ?s) i"
        proof (cases "i \<in> net_tree_ips p")
          assume "i \<in> net_tree_ips p"
          with `s\<in>init (pnet np p)` have "i\<in>net_ips s" ..
          hence "Some (the (fst (netgmap sr s) i)) = fst (netgmap sr s) i"
            by (rule some_the_fst_netgmap)
          with `i\<in>net_tree_ips p` show ?thesis
            by simp
        next
          assume "i \<notin> net_tree_ips p"
          moreover with `s\<in>init (pnet np p)` have "i\<notin>net_ips s" ..
          ultimately show ?thesis
            by simp
        qed
      qed simp
      ultimately show ?thesis
        by (rule rev_image_eqI)
    qed
    ultimately show ?thesis
      by (rule set_rev_mp [rotated])
  qed

lemma transfer_connect:
  assumes "(s, connect(i, i'), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), connect(i, i'), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms have "((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n)
                     \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>, snd (netgmap sr s'))"
      proof (induction n arbitrary: s s' \<zeta>)
        fix ii R\<^sub>i ns ns' \<zeta>
        assume "(ns, connect(i, i'), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
           and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
        from this(1) have "(ns, connect(i, i'), ns') \<in> node_sos (trans (np ii))"
          by (simp add: node_comps)
        moreover then obtain ni s s' R R' where "ns  = NodeS ni s R"
                                            and "ns' = NodeS ni s' R'" ..
        ultimately have "(NodeS ni s R, connect(i, i'), NodeS ni s' R') \<in> node_sos (trans (np ii))"
          by simp
        moreover then have "s' = s" by auto
        ultimately have "((\<sigma>, NodeS ni (snd (sr s)) R), connect(i, i'), (\<sigma>, NodeS ni (snd (sr s)) R'))
                                                                      \<in> onode_sos (trans (onp ii))"
          by - (rule node_connectTE', auto intro!: onode_sos.intros [simplified])
        with `ns = NodeS ni s R` `ns' = NodeS ni s' R'` `s' = s`
             and `netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)`
          show "((\<sigma>, snd (netgmap sr ns)), connect(i, i'), (\<sigma>, snd (netgmap sr ns'))) \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)
                \<and> netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, snd (netgmap sr ns'))"
            by (simp add: onode_comps)
      next
        fix n1 n2 s s' \<zeta>
        assume IH1: "\<And>s s' \<zeta>. (s, connect(i, i'), s') \<in> trans (pnet np n1)
                      \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                      \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                      \<Longrightarrow> wf_net_tree n1
                      \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n1)
                          \<and> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s'))"
           and IH2: "\<And>s s' \<zeta>. (s, connect(i, i'), s') \<in> trans (pnet np n2)
                      \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                      \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                      \<Longrightarrow> wf_net_tree n2
                      \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n2)
                          \<and> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s'))"
           and tr: "(s, connect(i, i'), s') \<in> trans (pnet np (n1 \<parallel> n2))"
           and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
           and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
           and "wf_net_tree (n1 \<parallel> n2)"
        from this(3) have "(s, connect(i, i'), s') \<in> pnet_sos (trans (pnet np n1))
                                                               (trans (pnet np n2))"
          by simp
        then obtain s1 s1' s2 s2' where "s = SubnetS s1 s2"
                                    and "s' = SubnetS s1' s2'"
                                    and "(s1, connect(i, i'), s1') \<in> trans (pnet np n1)"
                                    and "(s2, connect(i, i'), s2') \<in> trans (pnet np n2)"
          by (rule partial_connectTE) auto
        from this(1) and nm have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
          by simp

        from `wf_net_tree (n1 \<parallel> n2)` have "wf_net_tree n1" and "wf_net_tree n2"
                                      and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

        from sr `s = SubnetS s1 s2` have "s1 \<in> reachable (pnet np n1) TT" by (metis subnet_reachable(1))
        hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)

        from sr `s = SubnetS s1 s2` have "s2 \<in> reachable (pnet np n2) TT" by (metis subnet_reachable(2))
        hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)

        from nm `s = SubnetS s1 s2`
          have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)" by simp
        hence "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          using `net_tree_ips n1 \<inter> net_tree_ips n2 = {}` `net_ips s1 = net_tree_ips n1`
                and `net_ips s2 = net_tree_ips n2` by (rule netgmap_subnet_split1)
        with `(s1, connect(i, i'), s1') \<in> trans (pnet np n1)`
         and `s1 \<in> reachable (pnet np n1) TT`
         have "((\<sigma>, snd (netgmap sr s1)), connect(i, i'), (\<sigma>, snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
          and "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1'))"
           using `wf_net_tree n1` unfolding atomize_conj by (rule IH1)

        from `netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)`
             `net_ips s1 = net_tree_ips n1` and `net_ips s2 = net_tree_ips n2`
          have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
            by (rule netgmap_subnet_split2)
        with `(s2, connect(i, i'), s2') \<in> trans (pnet np n2)`
         and `s2 \<in> reachable (pnet np n2) TT`
         have "((\<sigma>, snd (netgmap sr s2)), connect(i, i'), (\<sigma>, snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
          and "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2'))"
           using `wf_net_tree n2` unfolding atomize_conj by (rule IH2)

        have "((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s')))
                                         \<in> trans (opnet onp (n1 \<parallel> n2))"
        proof -
          from `((\<sigma>, snd (netgmap sr s1)), connect(i, i'), (\<sigma>, snd (netgmap sr s1'))) \<in> trans (opnet onp n1)`
           and `((\<sigma>, snd (netgmap sr s2)), connect(i, i'), (\<sigma>, snd (netgmap sr s2'))) \<in> trans (opnet onp n2)`
            have "((\<sigma>, SubnetS (snd (netgmap sr s1)) (snd (netgmap sr s2))), connect(i, i'),
                   (\<sigma>, SubnetS (snd (netgmap sr s1')) (snd (netgmap sr s2'))))
                                           \<in> opnet_sos (trans (opnet onp n1)) (trans (opnet onp n2))"
              by (rule opnet_connect)
          with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` show ?thesis by simp
        qed

        moreover from `netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1'))`
                      `netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2'))`
                      `s' = SubnetS s1' s2'`
          have "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr s'))" ..

        ultimately show "((\<sigma>, snd (netgmap sr s)), connect(i, i'), (\<sigma>, snd (netgmap sr s')))
                                                                \<in> trans (opnet onp (n1 \<parallel> n2))
                         \<and> netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr s'))" ..
      qed
    moreover from `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)` have "\<zeta> = snd (netgmap sr s)" by simp
    ultimately show " \<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), connect(i, i'), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                              \<and> (\<forall>j. j \<notin> net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                              \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_disconnect:
  assumes "(s, disconnect(i, i'), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), disconnect(i, i'), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms have "((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n)
                     \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>, snd (netgmap sr s'))"
      proof (induction n arbitrary: s s' \<zeta>)
        fix ii R\<^sub>i ns ns' \<zeta>
        assume "(ns, disconnect(i, i'), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
           and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
        from this(1) have "(ns, disconnect(i, i'), ns') \<in> node_sos (trans (np ii))"
          by (simp add: node_comps)
        moreover then obtain ni s s' R R' where "ns  = NodeS ni s R"
                                            and "ns' = NodeS ni s' R'" ..
        ultimately have "(NodeS ni s R, disconnect(i, i'), NodeS ni s' R') \<in> node_sos (trans (np ii))"
          by simp
        moreover then have "s' = s" by auto
        ultimately have "((\<sigma>, NodeS ni (snd (sr s)) R), disconnect(i, i'), (\<sigma>, NodeS ni (snd (sr s)) R'))
                                                                      \<in> onode_sos (trans (onp ii))"
          by - (rule node_disconnectTE', auto intro!: onode_sos.intros [simplified])
        with `ns = NodeS ni s R` `ns' = NodeS ni s' R'` `s' = s`
             and `netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)`
          show "((\<sigma>, snd (netgmap sr ns)), disconnect(i, i'), (\<sigma>, snd (netgmap sr ns'))) \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)
                \<and> netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, snd (netgmap sr ns'))"
            by (simp add: onode_comps)
      next
        fix n1 n2 s s' \<zeta>
        assume IH1: "\<And>s s' \<zeta>. (s, disconnect(i, i'), s') \<in> trans (pnet np n1)
                      \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                      \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                      \<Longrightarrow> wf_net_tree n1
                      \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n1)
                          \<and> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s'))"
           and IH2: "\<And>s s' \<zeta>. (s, disconnect(i, i'), s') \<in> trans (pnet np n2)
                      \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                      \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                      \<Longrightarrow> wf_net_tree n2
                      \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s'))) \<in> trans (opnet onp n2)
                          \<and> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s'))"
           and tr: "(s, disconnect(i, i'), s') \<in> trans (pnet np (n1 \<parallel> n2))"
           and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
           and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
           and "wf_net_tree (n1 \<parallel> n2)"
        from this(3) have "(s, disconnect(i, i'), s') \<in> pnet_sos (trans (pnet np n1))
                                                               (trans (pnet np n2))"
          by simp
        then obtain s1 s1' s2 s2' where "s = SubnetS s1 s2"
                                    and "s' = SubnetS s1' s2'"
                                    and "(s1, disconnect(i, i'), s1') \<in> trans (pnet np n1)"
                                    and "(s2, disconnect(i, i'), s2') \<in> trans (pnet np n2)"
          by (rule partial_disconnectTE) auto
        from this(1) and nm have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
          by simp

        from `wf_net_tree (n1 \<parallel> n2)` have "wf_net_tree n1" and "wf_net_tree n2"
                                      and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

        from sr `s = SubnetS s1 s2` have "s1 \<in> reachable (pnet np n1) TT" by (metis subnet_reachable(1))
        hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)

        from sr `s = SubnetS s1 s2` have "s2 \<in> reachable (pnet np n2) TT" by (metis subnet_reachable(2))
        hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)

        from nm `s = SubnetS s1 s2`
          have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)" by simp
        hence "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          using `net_tree_ips n1 \<inter> net_tree_ips n2 = {}` `net_ips s1 = net_tree_ips n1`
                and `net_ips s2 = net_tree_ips n2` by (rule netgmap_subnet_split1)
        with `(s1, disconnect(i, i'), s1') \<in> trans (pnet np n1)`
         and `s1 \<in> reachable (pnet np n1) TT`
         have "((\<sigma>, snd (netgmap sr s1)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
          and "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1'))"
           using `wf_net_tree n1` unfolding atomize_conj by (rule IH1)

        from `netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)`
             `net_ips s1 = net_tree_ips n1` and `net_ips s2 = net_tree_ips n2`
          have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
            by (rule netgmap_subnet_split2)
        with `(s2, disconnect(i, i'), s2') \<in> trans (pnet np n2)`
         and `s2 \<in> reachable (pnet np n2) TT`
         have "((\<sigma>, snd (netgmap sr s2)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
          and "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2'))"
           using `wf_net_tree n2` unfolding atomize_conj by (rule IH2)

        have "((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s')))
                                         \<in> trans (opnet onp (n1 \<parallel> n2))"
        proof -
          from `((\<sigma>, snd (netgmap sr s1)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s1'))) \<in> trans (opnet onp n1)`
           and `((\<sigma>, snd (netgmap sr s2)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s2'))) \<in> trans (opnet onp n2)`
            have "((\<sigma>, SubnetS (snd (netgmap sr s1)) (snd (netgmap sr s2))), disconnect(i, i'),
                   (\<sigma>, SubnetS (snd (netgmap sr s1')) (snd (netgmap sr s2'))))
                                           \<in> opnet_sos (trans (opnet onp n1)) (trans (opnet onp n2))"
              by (rule opnet_disconnect)
          with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` show ?thesis by simp
        qed

        moreover from `netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1'))`
                      `netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2'))`
                      `s' = SubnetS s1' s2'`
          have "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr s'))" ..

        ultimately show "((\<sigma>, snd (netgmap sr s)), disconnect(i, i'), (\<sigma>, snd (netgmap sr s')))
                                                                \<in> trans (opnet onp (n1 \<parallel> n2))
                         \<and> netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr s'))" ..
      qed
    moreover from `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)` have "\<zeta> = snd (netgmap sr s)" by simp
    ultimately show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), disconnect(i, i'), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                              \<and> (\<forall>j. j \<notin> net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                              \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_tau:
  assumes "(s, \<tau>, s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), \<tau>, (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms(4,2,1) obtain i where "i\<in>net_ips s"
                                 and "\<forall>j. j\<noteq>i \<longrightarrow> netmap s' j = netmap s j"
                                 and "net_ip_action np \<tau> i n s s'"
      by (metis pnet_tau_single_node)
    from this(2) have "\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j"
      by (clarsimp intro!: netmap_is_fst_netgmap')
    from `(s, \<tau>, s') \<in> trans (pnet np n)` have "net_ips s' = net_ips s"
      by (rule pnet_maintains_dom [THEN sym])
    def \<sigma>' \<equiv> "\<lambda>j. if j = i then the (fst (netgmap sr s') i) else \<sigma> j"
    from `\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j`
         and `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)`
      have "\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j"
        unfolding \<sigma>'_def by clarsimp

    from assms(2) have "net_ips s = net_tree_ips n"
      by (rule pnet_net_ips_net_tree_ips)

    from `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)`
      have "\<zeta> = snd (netgmap sr s)" by simp

    from `\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j` `i \<in> net_ips s`
         `net_ips s = net_tree_ips n` `net_ips s' = net_ips s`
         `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)`
      have "fst (netgmap sr s') = fst (netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s')))"
        unfolding \<sigma>'_def by - (rule ext, clarsimp)

    hence "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
      by (rule prod_eqI, simp)

    with assms(1, 3)
      have "((\<sigma>, snd (netgmap sr s)), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
        using assms(2,4) `i\<in>net_ips s` and `net_ip_action np \<tau> i n s s'`
    proof (induction n arbitrary: s s' \<zeta>)
      fix ii R\<^sub>i ns ns' \<zeta>
      assume "(ns, \<tau>, ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
         and nsr: "ns \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
         and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
         and "netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))"
         and "i\<in>net_ips ns"
      from this(1) have "(ns, \<tau>, ns') \<in> node_sos (trans (np ii))"
        by (simp add: node_comps)
      moreover with nsr obtain s s' R R' where "ns  = NodeS ii s R"
                                           and "ns' = NodeS ii s' R'"
         by (metis net_node_reachable_is_node node_tauTE')
      moreover from `i \<in> net_ips ns` and `ns  = NodeS ii s R` have "ii = i" by simp
      ultimately have ntr: "(NodeS i s R, \<tau>, NodeS i s' R') \<in> node_sos (trans (np i))"
        by simp
      hence "R' = R" by (metis net_state.inject(1) node_tauTE')

      from ntr obtain a where "(s, a, s') \<in> trans (np i)"
                          and "(\<exists>d. a = \<not>unicast d \<and> d\<notin>R) \<or> (a = \<tau>)"
        by (rule node_tauTE') auto

      from `netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)` `ns  = NodeS ii s R` and `ii = i`
        have "\<sigma> i = fst (sr s)" by simp (metis map_upd_Some_unfold)

      moreover from `netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))`
                    `ns' = NodeS ii s' R'` and `ii = i`
        have "\<sigma>' i = fst (sr s')"
          unfolding \<sigma>'_def by clarsimp (metis (full_types, lifting) fun_upd_same option.sel) 
      ultimately have "((\<sigma>, snd (sr s)), a, (\<sigma>', snd (sr s'))) \<in> trans (onp i)"
        using `(s, a, s') \<in> trans (np i)` by (rule trans)

      from `(\<exists>d. a = \<not>unicast d \<and> d\<notin>R) \<or> (a = \<tau>)` `\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j` `R'=R`
           and `((\<sigma>, snd (sr s)), a, (\<sigma>', snd (sr s'))) \<in> trans (onp i)`
        have "((\<sigma>, NodeS i (snd (sr s)) R), \<tau>, (\<sigma>', NodeS i (snd (sr s')) R')) \<in> onode_sos (trans (onp i))"
          by (metis onode_sos.onode_notucast onode_sos.onode_tau)

      with `ns  = NodeS ii s R` `ns' = NodeS ii s' R'` `ii = i`
        show "((\<sigma>, snd (netgmap sr ns)), \<tau>, (\<sigma>', snd (netgmap sr ns'))) \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)"
          by (simp add: onode_comps)
    next
      fix n1 n2 s s' \<zeta>
      assume IH1: "\<And>s s' \<zeta>. (s, \<tau>, s') \<in> trans (pnet np n1)
                    \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                    \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s'))
                    \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                    \<Longrightarrow> wf_net_tree n1
                    \<Longrightarrow> i\<in>net_ips s
                    \<Longrightarrow> net_ip_action np \<tau> i n1 s s'
                    \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n1)"
         and IH2: "\<And>s s' \<zeta>. (s, \<tau>, s') \<in> trans (pnet np n2)
                    \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                    \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s'))
                    \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                    \<Longrightarrow> wf_net_tree n2
                    \<Longrightarrow> i\<in>net_ips s
                    \<Longrightarrow> net_ip_action np \<tau> i n2 s s'
                    \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n2)"
         and tr: "(s, \<tau>, s') \<in> trans (pnet np (n1 \<parallel> n2))"
         and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
         and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
         and nm': "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
         and "wf_net_tree (n1 \<parallel> n2)"
         and "i\<in>net_ips s"
         and "net_ip_action np \<tau> i (n1 \<parallel> n2) s s'"
      from tr have "(s, \<tau>, s') \<in> pnet_sos (trans (pnet np n1)) (trans (pnet np n2))" by simp
      then obtain s1 s1' s2 s2' where "s = SubnetS s1 s2"
                                  and "s' = SubnetS s1' s2'"
        by (rule partial_tauTE) auto
      from this(1) and nm have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
        by simp
      from `s' = SubnetS s1' s2'` and nm'
        have "netgmap sr (SubnetS s1' s2') = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
          by simp

      from `wf_net_tree (n1 \<parallel> n2)` have "wf_net_tree n1"
                                    and "wf_net_tree n2"
                                    and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

      from sr [simplified `s = SubnetS s1 s2`] have "s1 \<in> reachable (pnet np n1) TT"
        by (rule subnet_reachable(1))
      hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)

      from sr [simplified `s = SubnetS s1 s2`] have "s2 \<in> reachable (pnet np n2) TT"
        by (rule subnet_reachable(2))
      hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)

      from nm [simplified `s = SubnetS s1 s2`]
           `net_tree_ips n1 \<inter> net_tree_ips n2 = {}`
           `net_ips s1 = net_tree_ips n1`
           `net_ips s2 = net_tree_ips n2` 
        have "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          by (rule netgmap_subnet_split1)

      from nm [simplified `s = SubnetS s1 s2`]
           `net_ips s1 = net_tree_ips n1`
           `net_ips s2 = net_tree_ips n2` 
        have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
          by (rule netgmap_subnet_split2)

      from `i\<in>net_ips s` and `s = SubnetS s1 s2` have "i\<in>net_ips s1 \<or> i\<in>net_ips s2" by auto
        thus "((\<sigma>, snd (netgmap sr s)), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp (n1 \<parallel> n2))"
      proof
        assume "i\<in>net_ips s1"
        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` `net_ip_action np \<tau> i (n1 \<parallel> n2) s s'`
          have "(s1, \<tau>, s1') \<in> trans (pnet np n1)"
           and "net_ip_action np \<tau> i n1 s1 s1'"
           and "s2' = s2" by simp_all

        from `net_ips s1 = net_tree_ips n1` and `(s1, \<tau>, s1') \<in> trans (pnet np n1)`
          have "net_ips s1' = net_tree_ips n1" by (metis pnet_maintains_dom)

        from nm' [simplified `s' = SubnetS s1' s2'` `s2' = s2`]
                        `net_tree_ips n1 \<inter> net_tree_ips n2 = {}`
                        `net_ips s1' = net_tree_ips n1`
                        `net_ips s2 = net_tree_ips n2`
          have "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))"
            by (rule netgmap_subnet_split1)

        from `(s1, \<tau>, s1') \<in> trans (pnet np n1)`
             `netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))`
             `netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))`
             `s1 \<in> reachable (pnet np n1) TT`
             `wf_net_tree n1`
             `i\<in>net_ips s1`
             `net_ip_action np \<tau> i n1 s1 s1'`
          have "((\<sigma>, snd (netgmap sr s1)), \<tau>, (\<sigma>', snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
             by (rule IH1)

        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` `s2' = s2` show ?thesis
          by (simp del: step_node_tau) (erule opnet_tau1)
      next
        assume "i\<in>net_ips s2"
        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` `net_ip_action np \<tau> i (n1 \<parallel> n2) s s'`
          have "(s2, \<tau>, s2') \<in> trans (pnet np n2)"
           and "net_ip_action np \<tau> i n2 s2 s2'"
           and "s1' = s1" by simp_all

        from `net_ips s2 = net_tree_ips n2` and `(s2, \<tau>, s2') \<in> trans (pnet np n2)`
          have "net_ips s2' = net_tree_ips n2" by (metis pnet_maintains_dom)

        from nm' [simplified `s' = SubnetS s1' s2'` `s1' = s1`]
                        `net_ips s1 = net_tree_ips n1`
                        `net_ips s2' = net_tree_ips n2`
          have "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))"
            by (rule netgmap_subnet_split2)

        from `(s2, \<tau>, s2') \<in> trans (pnet np n2)`
             `netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))`
             `netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))`
             `s2 \<in> reachable (pnet np n2) TT`
             `wf_net_tree n2`
             `i\<in>net_ips s2`
             `net_ip_action np \<tau> i n2 s2 s2'`
          have "((\<sigma>, snd (netgmap sr s2)), \<tau>, (\<sigma>', snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
             by (rule IH2)

        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` `s1' = s1` show ?thesis
          by (simp del: step_node_tau) (erule opnet_tau2)
      qed
    qed
    with `\<zeta> = snd (netgmap sr s)` have "((\<sigma>, \<zeta>), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      by simp
    moreover from `\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j` `i \<in> net_ips s` `\<zeta> = snd (netgmap sr s)`
      have "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j" by (metis net_ips_netgmap)
    ultimately have "((\<sigma>, \<zeta>), \<tau>, (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)
                     \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                     \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
      using `netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))` by simp
    thus "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), \<tau>, (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                  \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                  \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_deliver:
  assumes "(s, i:deliver(d), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), i:deliver(d), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms(4,2,1) obtain "i\<in>net_ips s"
                         and "\<forall>j. j\<noteq>i \<longrightarrow> netmap s' j = netmap s j"
                         and "net_ip_action np (i:deliver(d)) i n s s'"
      by (metis delivered_to_net_ips pnet_deliver_single_node)
    from this(2) have "\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j"
      by (clarsimp intro!: netmap_is_fst_netgmap')
    from `(s, i:deliver(d), s') \<in> trans (pnet np n)` have "net_ips s' = net_ips s"
      by (rule pnet_maintains_dom [THEN sym])
    def \<sigma>' \<equiv> "\<lambda>j. if j = i then the (fst (netgmap sr s') i) else \<sigma> j"
    from `\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j`
         and `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)`
      have "\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j"
        unfolding \<sigma>'_def by clarsimp

    from assms(2) have "net_ips s = net_tree_ips n"
      by (rule pnet_net_ips_net_tree_ips)

    from `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)`
      have "\<zeta> = snd (netgmap sr s)" by simp

    from `\<forall>j. j\<noteq>i \<longrightarrow> fst (netgmap sr s') j = fst (netgmap sr s) j` `i \<in> net_ips s`
         `net_ips s = net_tree_ips n` `net_ips s' = net_ips s`
         `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)`
      have "fst (netgmap sr s') = fst (netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s')))"
        unfolding \<sigma>'_def by - (rule ext, clarsimp)

    hence "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
      by (rule prod_eqI, simp)

    with assms(1, 3)
      have "((\<sigma>, snd (netgmap sr s)), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
        using assms(2,4) `i\<in>net_ips s` and `net_ip_action np (i:deliver(d)) i n s s'`
    proof (induction n arbitrary: s s' \<zeta>)
      fix ii R\<^sub>i ns ns' \<zeta>
      assume "(ns, i:deliver(d), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
         and nsr: "ns \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
         and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
         and "netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))"
         and "i\<in>net_ips ns"
      from this(1) have "(ns, i:deliver(d), ns') \<in> node_sos (trans (np ii))"
        by (simp add: node_comps)
      moreover with nsr obtain s s' R R' where "ns  = NodeS ii s R"
                                           and "ns' = NodeS ii s' R'"
         by (metis net_node_reachable_is_node node_sos_dest)
      moreover from `i \<in> net_ips ns` and `ns  = NodeS ii s R` have "ii = i" by simp
      ultimately have ntr: "(NodeS i s R, i:deliver(d), NodeS i s' R') \<in> node_sos (trans (np i))"
        by simp
      hence "R' = R" by (metis net_state.inject(1) node_deliverTE')

      from ntr have "(s, deliver d, s') \<in> trans (np i)"
        by (rule node_deliverTE') simp

      from `netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)` `ns  = NodeS ii s R` and `ii = i`
        have "\<sigma> i = fst (sr s)" by simp (metis map_upd_Some_unfold)

      moreover from `netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))`
                    `ns' = NodeS ii s' R'` and `ii = i`
        have "\<sigma>' i = fst (sr s')"
          unfolding \<sigma>'_def by clarsimp (metis (lifting, full_types) fun_upd_same option.sel)
      ultimately have "((\<sigma>, snd (sr s)), deliver d, (\<sigma>', snd (sr s'))) \<in> trans (onp i)"
        using `(s, deliver d, s') \<in> trans (np i)` by (rule trans)

      with `\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j` `R'=R`
        have "((\<sigma>, NodeS i (snd (sr s)) R), i:deliver(d), (\<sigma>', NodeS i (snd (sr s')) R'))
                                                                      \<in> onode_sos (trans (onp i))"
          by (metis onode_sos.onode_deliver)

      with `ns  = NodeS ii s R` `ns' = NodeS ii s' R'` `ii = i`
        show "((\<sigma>, snd (netgmap sr ns)), i:deliver(d), (\<sigma>', snd (netgmap sr ns'))) \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)"
          by (simp add: onode_comps)
    next
      fix n1 n2 s s' \<zeta>
      assume IH1: "\<And>s s' \<zeta>. (s, i:deliver(d), s') \<in> trans (pnet np n1)
                    \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                    \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s'))
                    \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                    \<Longrightarrow> wf_net_tree n1
                    \<Longrightarrow> i\<in>net_ips s
                    \<Longrightarrow> net_ip_action np (i:deliver(d)) i n1 s s'
                    \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n1)"
         and IH2: "\<And>s s' \<zeta>. (s, i:deliver(d), s') \<in> trans (pnet np n2)
                    \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                    \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s'))
                    \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                    \<Longrightarrow> wf_net_tree n2
                    \<Longrightarrow> i\<in>net_ips s
                    \<Longrightarrow> net_ip_action np (i:deliver(d)) i n2 s s'
                    \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n2)"
         and tr: "(s, i:deliver(d), s') \<in> trans (pnet np (n1 \<parallel> n2))"
         and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
         and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
         and nm': "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
         and "wf_net_tree (n1 \<parallel> n2)"
         and "i\<in>net_ips s"
         and "net_ip_action np (i:deliver(d)) i (n1 \<parallel> n2) s s'"
      from tr have "(s, i:deliver(d), s') \<in> pnet_sos (trans (pnet np n1)) (trans (pnet np n2))" by simp
      then obtain s1 s1' s2 s2' where "s = SubnetS s1 s2"
                                  and "s' = SubnetS s1' s2'"
        by (rule partial_deliverTE) auto
      from this(1) and nm have "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
        by simp
      from `s' = SubnetS s1' s2'` and nm'
        have "netgmap sr (SubnetS s1' s2') = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
          by simp

      from `wf_net_tree (n1 \<parallel> n2)` have "wf_net_tree n1"
                                    and "wf_net_tree n2"
                                    and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

      from sr [simplified `s = SubnetS s1 s2`] have "s1 \<in> reachable (pnet np n1) TT"
        by (rule subnet_reachable(1))
      hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)

      from sr [simplified `s = SubnetS s1 s2`] have "s2 \<in> reachable (pnet np n2) TT"
        by (rule subnet_reachable(2))
      hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)

      from nm [simplified `s = SubnetS s1 s2`]
           `net_tree_ips n1 \<inter> net_tree_ips n2 = {}`
           `net_ips s1 = net_tree_ips n1`
           `net_ips s2 = net_tree_ips n2` 
        have "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          by (rule netgmap_subnet_split1)

      from nm [simplified `s = SubnetS s1 s2`]
           `net_ips s1 = net_tree_ips n1`
           `net_ips s2 = net_tree_ips n2` 
        have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
          by (rule netgmap_subnet_split2)

      from `i\<in>net_ips s` and `s = SubnetS s1 s2` have "i\<in>net_ips s1 \<or> i\<in>net_ips s2" by auto
        thus "((\<sigma>, snd (netgmap sr s)), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp (n1 \<parallel> n2))"
      proof
        assume "i\<in>net_ips s1"
        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` `net_ip_action np (i:deliver(d)) i (n1 \<parallel> n2) s s'`
          have "(s1, i:deliver(d), s1') \<in> trans (pnet np n1)"
           and "net_ip_action np (i:deliver(d)) i n1 s1 s1'"
           and "s2' = s2" by simp_all

        from `net_ips s1 = net_tree_ips n1` and `(s1, i:deliver(d), s1') \<in> trans (pnet np n1)`
          have "net_ips s1' = net_tree_ips n1" by (metis pnet_maintains_dom)

        from nm' [simplified `s' = SubnetS s1' s2'` `s2' = s2`]
                        `net_tree_ips n1 \<inter> net_tree_ips n2 = {}`
                        `net_ips s1' = net_tree_ips n1`
                        `net_ips s2 = net_tree_ips n2`
          have "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))"
            by (rule netgmap_subnet_split1)

        from `(s1, i:deliver(d), s1') \<in> trans (pnet np n1)`
             `netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))`
             `netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))`
             `s1 \<in> reachable (pnet np n1) TT`
             `wf_net_tree n1`
             `i\<in>net_ips s1`
             `net_ip_action np (i:deliver(d)) i n1 s1 s1'`
          have "((\<sigma>, snd (netgmap sr s1)), i:deliver(d), (\<sigma>', snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
             by (rule IH1)

        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` `s2' = s2` show ?thesis
          by simp (erule opnet_deliver1)
      next
        assume "i\<in>net_ips s2"
        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` `net_ip_action np (i:deliver(d)) i (n1 \<parallel> n2) s s'`
          have "(s2, i:deliver(d), s2') \<in> trans (pnet np n2)"
           and "net_ip_action np (i:deliver(d)) i n2 s2 s2'"
           and "s1' = s1" by simp_all

        from `net_ips s2 = net_tree_ips n2` and `(s2, i:deliver(d), s2') \<in> trans (pnet np n2)`
          have "net_ips s2' = net_tree_ips n2" by (metis pnet_maintains_dom)

        from nm' [simplified `s' = SubnetS s1' s2'` `s1' = s1`]
                        `net_ips s1 = net_tree_ips n1`
                        `net_ips s2' = net_tree_ips n2`
          have "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))"
            by (rule netgmap_subnet_split2)

        from `(s2, i:deliver(d), s2') \<in> trans (pnet np n2)`
             `netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))`
             `netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))`
             `s2 \<in> reachable (pnet np n2) TT`
             `wf_net_tree n2`
             `i\<in>net_ips s2`
             `net_ip_action np (i:deliver(d)) i n2 s2 s2'`
          have "((\<sigma>, snd (netgmap sr s2)), i:deliver(d), (\<sigma>', snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
             by (rule IH2)

        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` `s1' = s1` show ?thesis
          by simp (erule opnet_deliver2)
      qed
    qed
    with `\<zeta> = snd (netgmap sr s)` have "((\<sigma>, \<zeta>), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      by simp
    moreover from `\<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j` `i \<in> net_ips s` `\<zeta> = snd (netgmap sr s)`
      have "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j" by (metis net_ips_netgmap)
    ultimately have "((\<sigma>, \<zeta>), i:deliver(d), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)
                     \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                     \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
      using `netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))` by simp
    thus "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), i:deliver(d), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                  \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                  \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_arrive':
  assumes "(s, H\<not>K:arrive(m), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s  = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
      and "wf_net_tree n"
  shows "((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
  proof -

    from assms(2) have "net_ips s = net_tree_ips n" ..
    with assms(1) have "net_ips s' = net_tree_ips n"
      by (metis pnet_maintains_dom)

    from `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)`
      have "\<zeta> = snd (netgmap sr s)" by simp

    from `netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')`
      have "\<zeta>' = snd (netgmap sr s')"
       and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
         by simp_all

    from assms(1-3) `netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))` assms(5)
      have "((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      proof (induction n arbitrary: s s' \<zeta> H K)
        fix ii R\<^sub>i ns ns' \<zeta> H K
        assume "(ns, H\<not>K:arrive(m), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
           and nsr: "ns \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
           and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
           and "netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))"
        from this(1) have "(ns, H\<not>K:arrive(m), ns') \<in> node_sos (trans (np ii))"
          by (simp add: node_comps)
        moreover with nsr obtain s s' R where "ns  = NodeS ii s R"
                                          and "ns' = NodeS ii s' R"
          by (metis net_node_reachable_is_node node_arriveTE')
        ultimately have "(NodeS ii s R, H\<not>K:arrive(m), NodeS ii s' R) \<in> node_sos (trans (np ii))"
          by simp
        from this(1) have "((\<sigma>, NodeS ii (snd (sr s)) R), H\<not>K:arrive(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
        proof (rule node_arriveTE)
          assume "(s, receive m, s') \<in> trans (np ii)"
             and "H = {ii}"
             and "K = {}"
          from `netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)` and `ns  = NodeS ii s R`
            have "\<sigma> ii = fst (sr s)"
              by simp (metis map_upd_Some_unfold)
          moreover from `netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))`
                        and `ns' = NodeS ii s' R`
            have "\<sigma>' ii = fst (sr s')" by simp (metis map_upd_Some_unfold)
          ultimately have "((\<sigma>, snd (sr s)), receive m, (\<sigma>', snd (sr s'))) \<in> trans (onp ii)"
            using `(s, receive m, s') \<in> trans (np ii)` by (rule trans)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), {ii}\<not>{}:arrive(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by (rule onode_receive)
          with `H={ii}` and `K={}`
            show "((\<sigma>, NodeS ii (snd (sr s)) R), H\<not>K:arrive(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
              by simp
        next
          assume "H = {}"
             and "s = s'"
             and "K = {ii}"
          from `s = s'` `netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))`
                        `netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)`
                        `ns = NodeS ii s R` and `ns' = NodeS ii s' R`
            have "\<sigma>' ii = \<sigma> ii" by simp (metis option.sel)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), {}\<not>{ii}:arrive(m), (\<sigma>', NodeS ii (snd (sr s)) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by (rule onode_arrive)
          with `H={}` `K={ii}` and `s = s'`
            show "((\<sigma>, NodeS ii (snd (sr s)) R), H\<not>K:arrive(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
              by simp
        qed
      with `ns = NodeS ii s R` `ns' = NodeS ii s' R`
        show "((\<sigma>, snd (netgmap sr ns)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr ns')))
                                                             \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)"
          by (simp add: onode_comps)
    next
      fix n1 n2 s s' \<zeta> H K
      assume IH1: "\<And>s s' \<zeta> H K. (s, H\<not>K:arrive(m), s') \<in> trans (pnet np n1)
                         \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                         \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                         \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s'))
                         \<Longrightarrow> wf_net_tree n1
                         \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), \<sigma>', snd (netgmap sr s'))
                                                                        \<in> trans (opnet onp n1)"
        and IH2: "\<And>s s' \<zeta> H K. (s, H\<not>K:arrive(m), s') \<in> trans (pnet np n2)
                         \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                         \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                         \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s'))
                         \<Longrightarrow> wf_net_tree n2
                         \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), \<sigma>', snd (netgmap sr s'))
                                                                        \<in> trans (opnet onp n2)"
        and "(s, H\<not>K:arrive(m), s') \<in> trans (pnet np (n1 \<parallel> n2))"
        and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
        and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
        and nm': "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
        and "wf_net_tree (n1 \<parallel> n2)"
      from this(3) have "(s, H\<not>K:arrive(m), s') \<in> pnet_sos (trans (pnet np n1))
                                                              (trans (pnet np n2))"
        by simp
      thus "((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s')))
                                                                   \<in> trans (opnet onp (n1 \<parallel> n2))"
      proof (rule partial_arriveTE)
        fix s1 s1' s2 s2' H1 H2 K1 K2
        assume "s = SubnetS s1 s2"
           and "s' = SubnetS s1' s2'"
           and tr1: "(s1, H1\<not>K1:arrive(m), s1') \<in> trans (pnet np n1)"
           and tr2: "(s2, H2\<not>K2:arrive(m), s2') \<in> trans (pnet np n2)"
           and "H = H1 \<union> H2"
           and "K = K1 \<union> K2"

        from `wf_net_tree (n1 \<parallel> n2)` have "wf_net_tree n1"
                                      and "wf_net_tree n2"
                                      and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

        from sr [simplified `s = SubnetS s1 s2`] have "s1 \<in> reachable (pnet np n1) TT"
          by (rule subnet_reachable(1))
        hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)
        with tr1 have "net_ips s1' = net_tree_ips n1" by (metis pnet_maintains_dom)

        from sr [simplified `s = SubnetS s1 s2`] have "s2 \<in> reachable (pnet np n2) TT"
          by (rule subnet_reachable(2))
        hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)
        with tr2 have "net_ips s2' = net_tree_ips n2" by (metis pnet_maintains_dom)

        from `(s1, H1\<not>K1:arrive(m), s1') \<in> trans (pnet np n1)`
             `s1 \<in> reachable (pnet np n1) TT`
          have "((\<sigma>, snd (netgmap sr s1)), H1\<not>K1:arrive(m), (\<sigma>', snd (netgmap sr s1')))
                                                                            \<in> trans (opnet onp n1)"
          proof (rule IH1 [OF _ _ _ _ `wf_net_tree n1`])
            from nm [simplified `s = SubnetS s1 s2`]
                 `net_tree_ips n1 \<inter> net_tree_ips n2 = {}`
                 `net_ips s1 = net_tree_ips n1`
                 `net_ips s2 = net_tree_ips n2` 
              show "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
                by (rule netgmap_subnet_split1)
          next
            from nm' [simplified `s' = SubnetS s1' s2'`]
                 `net_tree_ips n1 \<inter> net_tree_ips n2 = {}`
                 `net_ips s1' = net_tree_ips n1`
                 `net_ips s2' = net_tree_ips n2` 
              show "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))"
                by (rule netgmap_subnet_split1)
          qed

        moreover from `(s2, H2\<not>K2:arrive(m), s2') \<in> trans (pnet np n2)`
                      `s2 \<in> reachable (pnet np n2) TT`
          have "((\<sigma>, snd (netgmap sr s2)), H2\<not>K2:arrive(m), (\<sigma>', snd (netgmap sr s2')))
                                                                            \<in> trans (opnet onp n2)"
          proof (rule IH2 [OF _ _ _ _ `wf_net_tree n2`])
            from nm [simplified `s = SubnetS s1 s2`]
                 `net_ips s1 = net_tree_ips n1`
                 `net_ips s2 = net_tree_ips n2` 
              show "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
                by (rule netgmap_subnet_split2)
          next
            from nm' [simplified `s' = SubnetS s1' s2'`]
                 `net_ips s1' = net_tree_ips n1`
                 `net_ips s2' = net_tree_ips n2` 
              show "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))"
                by (rule netgmap_subnet_split2)
          qed
        ultimately show "((\<sigma>, snd (netgmap sr s)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s')))
                                                                     \<in> trans (opnet onp (n1 \<parallel> n2))"
          using `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` `H = H1 \<union> H2` `K = K1 \<union> K2`
            by simp (rule opnet_sos.opnet_arrive)
      qed
    qed
    with `\<zeta> = snd (netgmap sr s)` and `\<zeta>' = snd (netgmap sr s')`
      show "((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
        by simp
  qed

lemma transfer_arrive:
  assumes "(s, H\<not>K:arrive(m), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s  = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    def \<sigma>' \<equiv> "\<lambda>i. if i\<in>net_tree_ips n then the (fst (netgmap sr s') i) else \<sigma> i"

    from assms(2) have "net_ips s = net_tree_ips n"
      by (rule pnet_net_ips_net_tree_ips)
    with assms(1) have "net_ips s' = net_tree_ips n"
      by (metis pnet_maintains_dom)

    have "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
    proof (rule prod_eqI)
      from `net_ips s' = net_tree_ips n`
        show "fst (netgmap sr s') = fst (netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s')))"
          unfolding \<sigma>'_def by - (rule ext, clarsimp)
    qed simp

    moreover with assms(1-3)
    have "((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      using `wf_net_tree n` by (rule transfer_arrive')

    moreover have "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
    proof -
      have "\<forall>j. j\<notin>net_tree_ips n \<longrightarrow> \<sigma>' j = \<sigma> j" unfolding \<sigma>'_def by simp
      with assms(3) and `net_ips s = net_tree_ips n`
        show ?thesis
          by clarsimp (metis (mono_tags) net_ips_netgmap snd_conv)
    qed

    ultimately show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), H\<not>K:arrive(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                          \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                          \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')" by auto
  qed

lemma transfer_cast:
  assumes "(s, mR:*cast(m), s') \<in> trans (pnet np n)"
      and "s \<in> reachable (pnet np n) TT"
      and "netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)"
      and "wf_net_tree n"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), mR:*cast(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
  proof atomize_elim
    def \<sigma>' \<equiv> "\<lambda>i. if i\<in>net_tree_ips n then the (fst (netgmap sr s') i) else \<sigma> i"

    from assms(2) have "net_ips s = net_tree_ips n" ..
    with assms(1) have "net_ips s' = net_tree_ips n"
      by (metis pnet_maintains_dom)
    have "netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))"
    proof (rule prod_eqI)
      from `net_ips s' = net_tree_ips n`
        show "fst (netgmap sr s') = fst (netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s')))"
      unfolding \<sigma>'_def by - (rule ext, clarsimp simp add: some_the_fst_netgmap)
    qed simp

    from `net_ips s' = net_tree_ips n` and `net_ips s = net_tree_ips n` 
      have "\<forall>j. j\<notin>net_ips (snd (netgmap sr s)) \<longrightarrow> \<sigma>' j = \<sigma> j"
        unfolding \<sigma>'_def by simp

    from `netgmap sr s = netmask (net_tree_ips n) (\<sigma>, \<zeta>)`
      have "\<zeta> = snd (netgmap sr s)" by simp

    from assms(1-3) `netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))` assms(4)
      have "((\<sigma>, snd (netgmap sr s)), mR:*cast(m), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      proof (induction n arbitrary: s s' \<zeta> mR)
        fix ii R\<^sub>i ns ns' \<zeta> mR
        assume "(ns, mR:*cast(m), ns') \<in> trans (pnet np \<langle>ii; R\<^sub>i\<rangle>)"
           and nsr: "ns \<in> reachable (pnet np \<langle>ii; R\<^sub>i\<rangle>) TT"
           and "netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)"
           and "netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))"
        from this(1) have "(ns, mR:*cast(m), ns') \<in> node_sos (trans (np ii))"
          by (simp add: node_comps)
        moreover with nsr obtain s s' R where "ns  = NodeS ii s R"
                                          and "ns' = NodeS ii s' R"
          by (metis net_node_reachable_is_node node_castTE')
        ultimately have "(NodeS ii s R, mR:*cast(m), NodeS ii s' R) \<in> node_sos (trans (np ii))"
          by simp

        from `netgmap sr ns = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>, \<zeta>)` and `ns  = NodeS ii s R`
          have "\<sigma> ii = fst (sr s)"
            by simp (metis map_upd_Some_unfold)
        from `netgmap sr ns' = netmask (net_tree_ips \<langle>ii; R\<^sub>i\<rangle>) (\<sigma>', snd (netgmap sr ns'))`
             and `ns' = NodeS ii s' R`
          have "\<sigma>' ii = fst (sr s')" by simp (metis map_upd_Some_unfold)

        from `(NodeS ii s R, mR:*cast(m), NodeS ii s' R) \<in> node_sos (trans (np ii))`
          have "((\<sigma>, NodeS ii (snd (sr s)) R), mR:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
        proof (rule node_castTE)
          assume "(s, broadcast m, s') \<in> trans (np ii)"
             and "R = mR"
          from `\<sigma> ii = fst (sr s)` `\<sigma>' ii = fst (sr s')` and this(1)
            have "((\<sigma>, snd (sr s)), broadcast m, (\<sigma>', snd (sr s'))) \<in> trans (onp ii)"
              by (rule trans)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), R:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by (rule onode_bcast)
          with `R=mR` show "((\<sigma>, NodeS ii (snd (sr s)) R), mR:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
              by simp
        next
          fix D
          assume "(s, groupcast D m, s') \<in> trans (np ii)"
             and "mR = R \<inter> D"
          from `\<sigma> ii = fst (sr s)` `\<sigma>' ii = fst (sr s')` and this(1)
            have "((\<sigma>, snd (sr s)), groupcast D m, (\<sigma>', snd (sr s'))) \<in> trans (onp ii)"
              by (rule trans)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), (R \<inter> D):*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by (rule onode_gcast)
          with `mR = R \<inter> D` show "((\<sigma>, NodeS ii (snd (sr s)) R), mR:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
              by simp
        next
          fix d
          assume "(s, unicast d m, s') \<in> trans (np ii)"
             and "d \<in> R"
             and "mR = {d}"
          from `\<sigma> ii = fst (sr s)` `\<sigma>' ii = fst (sr s')` and this(1)
            have "((\<sigma>, snd (sr s)), unicast d m, (\<sigma>', snd (sr s'))) \<in> trans (onp ii)"
              by (rule trans)
          hence "((\<sigma>, NodeS ii (snd (sr s)) R), {d}:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            using `d\<in>R` by (rule onode_ucast)
          with `mR={d}` show "((\<sigma>, NodeS ii (snd (sr s)) R), mR:*cast(m), (\<sigma>', NodeS ii (snd (sr s')) R))
                                                                      \<in> onode_sos (trans (onp ii))"
            by simp
        qed
      with `ns = NodeS ii s R` `ns' = NodeS ii s' R`
        show "((\<sigma>, snd (netgmap sr ns)), mR:*cast(m), (\<sigma>', snd (netgmap sr ns')))
                                                             \<in> trans (opnet onp \<langle>ii; R\<^sub>i\<rangle>)"
          by (simp add: onode_comps)
    next
      fix n1 n2 s s' \<zeta> mR
      assume IH1: "\<And>s s' \<zeta> mR. (s, mR:*cast(m), s') \<in> trans (pnet np n1)
                         \<Longrightarrow> s \<in> reachable (pnet np n1) TT
                         \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n1) (\<sigma>, \<zeta>)
                         \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s'))
                         \<Longrightarrow> wf_net_tree n1
                         \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), mR:*cast(m), \<sigma>', snd (netgmap sr s'))
                                                                        \<in> trans (opnet onp n1)"
        and IH2: "\<And>s s' \<zeta> mR. (s, mR:*cast(m), s') \<in> trans (pnet np n2)
                         \<Longrightarrow> s \<in> reachable (pnet np n2) TT
                         \<Longrightarrow> netgmap sr s = netmask (net_tree_ips n2) (\<sigma>, \<zeta>)
                         \<Longrightarrow> netgmap sr s' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s'))
                         \<Longrightarrow> wf_net_tree n2
                         \<Longrightarrow> ((\<sigma>, snd (netgmap sr s)), mR:*cast(m), \<sigma>', snd (netgmap sr s'))
                                                                        \<in> trans (opnet onp n2)"
        and "(s, mR:*cast(m), s') \<in> trans (pnet np (n1 \<parallel> n2))"
        and sr: "s \<in> reachable (pnet np (n1 \<parallel> n2)) TT"
        and nm: "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
        and nm': "netgmap sr s' = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>', snd (netgmap sr s'))"
        and "wf_net_tree (n1 \<parallel> n2)"
      from this(3) have "(s, mR:*cast(m), s') \<in> pnet_sos (trans (pnet np n1)) (trans (pnet np n2))"
        by simp
      then obtain s1 s1' s2 s2' H K
        where "s  = SubnetS s1  s2"
          and "s' = SubnetS s1' s2'"
          and "H \<subseteq> mR"
          and "K \<inter> mR = {}"
          and trtr: "((s1, mR:*cast(m), s1') \<in> trans (pnet np n1)
                                  \<and> (s2, H\<not>K:arrive(m), s2') \<in> trans (pnet np n2))
                    \<or> ((s1, H\<not>K:arrive(m), s1') \<in> trans (pnet np n1)
                                  \<and> (s2, mR:*cast(m), s2') \<in> trans (pnet np n2))"
          by (rule partial_castTE) metis+

      from `wf_net_tree (n1 \<parallel> n2)` have "wf_net_tree n1"
                                    and "wf_net_tree n2"
                                    and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}" by auto

      from sr [simplified `s = SubnetS s1 s2`] have "s1 \<in> reachable (pnet np n1) TT"
        by (rule subnet_reachable(1))
      hence "net_ips s1 = net_tree_ips n1" by (rule pnet_net_ips_net_tree_ips)
      with trtr have "net_ips s1' = net_tree_ips n1" by (metis pnet_maintains_dom)

      from sr [simplified `s = SubnetS s1 s2`] have "s2 \<in> reachable (pnet np n2) TT"
        by (rule subnet_reachable(2))
      hence "net_ips s2 = net_tree_ips n2" by (rule pnet_net_ips_net_tree_ips)
      with trtr have "net_ips s2' = net_tree_ips n2" by (metis pnet_maintains_dom)

      from nm [simplified `s = SubnetS s1 s2`]
           `net_tree_ips n1 \<inter> net_tree_ips n2 = {}`
           `net_ips s1 = net_tree_ips n1`
           `net_ips s2 = net_tree_ips n2` 
        have "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
          by (rule netgmap_subnet_split1)

      from nm' [simplified `s' = SubnetS s1' s2'`]
           `net_tree_ips n1 \<inter> net_tree_ips n2 = {}`
           `net_ips s1' = net_tree_ips n1`
           `net_ips s2' = net_tree_ips n2` 
        have "netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))"
          by (rule netgmap_subnet_split1)

      from nm [simplified `s = SubnetS s1 s2`]
           `net_ips s1 = net_tree_ips n1`
           `net_ips s2 = net_tree_ips n2` 
        have "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
          by (rule netgmap_subnet_split2)

      from nm' [simplified `s' = SubnetS s1' s2'`]
           `net_ips s1' = net_tree_ips n1`
           `net_ips s2' = net_tree_ips n2` 
        have "netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))"
          by (rule netgmap_subnet_split2)

      from trtr show "((\<sigma>, snd (netgmap sr s)), mR:*cast(m), (\<sigma>', snd (netgmap sr s')))
                                                              \<in> trans (opnet onp (n1 \<parallel> n2))"
      proof (elim disjE conjE)
        assume "(s1, mR:*cast(m), s1') \<in> trans (pnet np n1)"
           and "(s2, H\<not>K:arrive(m), s2') \<in> trans (pnet np n2)"
        from `(s1, mR:*cast(m), s1') \<in> trans (pnet np n1)`
             `s1 \<in> reachable (pnet np n1) TT`
             `netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))`
             `netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))`
             `wf_net_tree n1`
          have "((\<sigma>, snd (netgmap sr s1)), mR:*cast(m), (\<sigma>', snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
            by (rule IH1)

        moreover from `(s2, H\<not>K:arrive(m), s2') \<in> trans (pnet np n2)`
             `s2 \<in> reachable (pnet np n2) TT`
             `netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))`
             `netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))`
             `wf_net_tree n2`
          have "((\<sigma>, snd (netgmap sr s2)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
            by (rule transfer_arrive')

        ultimately have "((\<sigma>, SubnetS (snd (netgmap sr s1)) (snd (netgmap sr s2))), mR:*cast(m),
                          (\<sigma>', SubnetS (snd (netgmap sr s1')) (snd (netgmap sr s2'))))
                             \<in> opnet_sos (trans (opnet onp n1)) (trans (opnet onp n2))"
          using `H \<subseteq> mR` and `K \<inter> mR = {}` by (rule opnet_sos.intros(1))
        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` show ?thesis by simp
      next
        assume "(s1, H\<not>K:arrive(m), s1') \<in> trans (pnet np n1)"
           and "(s2, mR:*cast(m), s2') \<in> trans (pnet np n2)"
        from `(s1, H\<not>K:arrive(m), s1') \<in> trans (pnet np n1)`
             `s1 \<in> reachable (pnet np n1) TT`
             `netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))`
             `netgmap sr s1' = netmask (net_tree_ips n1) (\<sigma>', snd (netgmap sr s1'))`
             `wf_net_tree n1`
          have "((\<sigma>, snd (netgmap sr s1)), H\<not>K:arrive(m), (\<sigma>', snd (netgmap sr s1'))) \<in> trans (opnet onp n1)"
            by (rule transfer_arrive')

        moreover from `(s2, mR:*cast(m), s2') \<in> trans (pnet np n2)`
             `s2 \<in> reachable (pnet np n2) TT`
             `netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))`
             `netgmap sr s2' = netmask (net_tree_ips n2) (\<sigma>', snd (netgmap sr s2'))`
             `wf_net_tree n2`
          have "((\<sigma>, snd (netgmap sr s2)), mR:*cast(m), (\<sigma>', snd (netgmap sr s2'))) \<in> trans (opnet onp n2)"
            by (rule IH2)

        ultimately have "((\<sigma>, SubnetS (snd (netgmap sr s1)) (snd (netgmap sr s2))), mR:*cast(m),
                          (\<sigma>', SubnetS (snd (netgmap sr s1')) (snd (netgmap sr s2'))))
                             \<in> opnet_sos (trans (opnet onp n1)) (trans (opnet onp n2))"
          using `H \<subseteq> mR` and `K \<inter> mR = {}` by (rule opnet_sos.intros(2))
        with `s = SubnetS s1 s2` `s' = SubnetS s1' s2'` show ?thesis by simp
      qed
    qed
    with `\<zeta> = snd (netgmap sr s)` have "((\<sigma>, \<zeta>), mR:*cast(m), (\<sigma>', snd (netgmap sr s'))) \<in> trans (opnet onp n)"
      by simp
    moreover from `\<forall>j. j\<notin>net_ips (snd (netgmap sr s)) \<longrightarrow> \<sigma>' j = \<sigma> j` `\<zeta> = snd (netgmap sr s)`
      have "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j" by simp
    moreover note `netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', snd (netgmap sr s'))`
    ultimately show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), mR:*cast(m), (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)
                           \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                           \<and> netgmap sr s' = netmask (net_tree_ips n) (\<sigma>', \<zeta>')"
      by auto
  qed

lemma transfer_pnet_action:
  assumes "s \<in> reachable (pnet np any) TT"
      and "netgmap sr s = netmask (net_tree_ips any) (\<sigma>, \<zeta>)"
      and "wf_net_tree any"
      and "(s, a, s') \<in> trans (pnet np any)"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (opnet onp any)"
                  and "\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
                  and "netgmap sr s' = netmask (net_tree_ips any) (\<sigma>', \<zeta>')"
  proof atomize_elim
    show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (opnet onp any)
                  \<and> (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                  \<and> netgmap sr s' = netmask (net_tree_ips any) (\<sigma>', \<zeta>')"
    proof (cases a)
      case node_cast
      with assms(4) show ?thesis
        by (auto elim!: transfer_cast [OF _ assms(1-3)])
    next
      case node_deliver
      with assms(4) show ?thesis
        by (auto elim!: transfer_deliver [OF _ assms(1-3)])
    next
      case node_arrive
      with assms(4) show ?thesis
        by (auto elim!: transfer_arrive [OF _ assms(1-3)])
    next
      case node_connect
      with assms(4) show ?thesis
        by (auto elim!: transfer_connect [OF _ assms(1-3)])
    next
      case node_disconnect
      with assms(4) show ?thesis
        by (auto elim!: transfer_disconnect [OF _ assms(1-3)])
    next
      case node_newpkt
      with assms(4) have False by (metis pnet_never_newpkt)
      thus ?thesis ..
    next
      case node_tau
      with assms(4) show ?thesis
        by (auto elim!: transfer_tau [OF _ assms(1-3), simplified])
    qed
  qed

lemma transfer_action_pnet_closed:
  assumes "(s, a, s') \<in> trans (closed (pnet np any))"
  obtains a' where "(s, a', s') \<in> trans (pnet np any)"
               and "\<And>\<sigma> \<zeta> \<sigma>' \<zeta>'. \<lbrakk> ((\<sigma>, \<zeta>), a', (\<sigma>', \<zeta>')) \<in> trans (opnet onp any);
                                  (\<forall>j. j\<notin>net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j) \<rbrakk>
                            \<Longrightarrow> ((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp any))"
  proof (atomize_elim)
    from assms have "(s, a, s') \<in> cnet_sos (trans (pnet np any))" by simp
    thus "\<exists>a'. (s, a', s') \<in> trans (pnet np any)
                \<and> (\<forall>\<sigma> \<zeta> \<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), a', (\<sigma>', \<zeta>')) \<in> trans (opnet onp any)
                               \<longrightarrow> (\<forall>j. j \<notin> net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j)
                               \<longrightarrow> ((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp any)))"
    proof cases
      case (cnet_cast R m) thus ?thesis
      by (auto intro!: exI [where x="R:*cast(m)"] dest!: ocnet_cast)
    qed (auto intro!: ocnet_sos.intros [simplified])
  qed

lemma transfer_action:
  assumes "s \<in> reachable (closed (pnet np any)) TT"
      and "netgmap sr s = netmask (net_tree_ips any) (\<sigma>, \<zeta>)"
      and "wf_net_tree any"
      and "(s, a, s') \<in> trans (closed (pnet np any))"
  obtains \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp any))"
                  and "netgmap sr s' = netmask (net_tree_ips any) (\<sigma>', \<zeta>')"
  proof atomize_elim
    from assms(1) have "s \<in> reachable (pnet np any) TT" ..
    from assms(4)
      show "\<exists>\<sigma>' \<zeta>'. ((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp any))
                    \<and> netgmap sr s' = netmask (net_tree_ips any) (\<sigma>', \<zeta>')"
        by (cases a)
           ((elim transfer_action_pnet_closed
                  transfer_pnet_action [OF `s \<in> reachable (pnet np any) TT` assms(2-3)])?,
            (auto intro!: exI)[1])+
  qed

lemma pnet_reachable_transfer':
  assumes "wf_net_tree any"
      and "s \<in> reachable (closed (pnet np any)) TT"
    shows "netgmap sr s \<in> netmask (net_tree_ips any) ` oreachable (oclosed (opnet onp any)) (\<lambda>_ _ _. True) U"
          (is " _ \<in> ?f ` ?oreachable any")
  using assms(2) proof induction
    fix s
    assume "s \<in> init (closed (pnet np any))"
    hence "s \<in> init (pnet np any)" by simp
    with `wf_net_tree any` have "netgmap sr s \<in> netmask (net_tree_ips any) ` init (opnet onp any)"
      by (rule init_pnet_opnet)
    hence "netgmap sr s \<in> netmask (net_tree_ips any) ` init (oclosed (opnet onp any))"
      by simp
    moreover have "netmask (net_tree_ips any) ` init (oclosed (opnet onp any))
                                        \<subseteq> netmask (net_tree_ips any) ` ?oreachable any"
      by (intro image_mono subsetI) (rule oreachable_init)
    ultimately show "netgmap sr s \<in> netmask (net_tree_ips any) ` ?oreachable any"
      by (rule set_rev_mp)
  next
    fix s a s'
    assume "s \<in> reachable (closed (pnet np any)) TT"
       and "netgmap sr s \<in> netmask (net_tree_ips any) ` ?oreachable any"
       and "(s, a, s') \<in> trans (closed (pnet np any))"
    from this(2) obtain \<sigma> \<zeta> where "netgmap sr s = netmask (net_tree_ips any) (\<sigma>, \<zeta>)"
                              and "(\<sigma>, \<zeta>) \<in> ?oreachable any"
      by clarsimp
    from `s \<in> reachable (closed (pnet np any)) TT` this(1) `wf_net_tree any`
         and `(s, a, s') \<in> trans (closed (pnet np any))`
      obtain \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp any))"
                     and "netgmap sr s' = netmask (net_tree_ips any) (\<sigma>', \<zeta>')"
        by (rule transfer_action)
    from `(\<sigma>, \<zeta>) \<in> ?oreachable any` and this(1) have "(\<sigma>', \<zeta>') \<in> ?oreachable any"
      by (rule oreachable_local) simp
    with `netgmap sr s' = netmask (net_tree_ips any) (\<sigma>', \<zeta>')`
      show "netgmap sr s' \<in> netmask (net_tree_ips any) ` ?oreachable any" by (rule image_eqI)
  qed

definition
  someinit :: "nat \<Rightarrow> 'g"
where
  "someinit i \<equiv> SOME x. x \<in> (fst o sr) ` init (np i)"

definition
  initmissing :: "((nat \<Rightarrow> 'g option) \<times> 'a) \<Rightarrow> (nat \<Rightarrow> 'g) \<times> 'a"
where
  "initmissing \<sigma> = (\<lambda>i. case (fst \<sigma>) i of None \<Rightarrow> someinit i | Some s \<Rightarrow> s, snd \<sigma>)"

lemma initmissing_def':
  "initmissing = apfst (default someinit)"
  by (auto simp add: initmissing_def default_def)

lemma netmask_initmissing_netgmap:
  "netmask (net_ips s) (initmissing (netgmap sr s)) = netgmap sr s"
  proof (intro prod_eqI ext)
    fix i
    show "fst (netmask (net_ips s) (initmissing (netgmap sr s))) i = fst (netgmap sr s) i"
      unfolding initmissing_def by (clarsimp split: option.split)
  qed (simp add: initmissing_def)

lemma snd_initmissing [simp]:
  "snd (initmissing x)= snd x"
  using assms unfolding initmissing_def by simp

lemma initmnissing_snd_netgmap [simp]:
  assumes "initmissing (netgmap sr s) = (\<sigma>, \<zeta>)"
    shows "snd (netgmap sr s) = \<zeta>"
  using assms unfolding initmissing_def by simp


lemma in_net_ips_fst_init_missing [simp]:
  assumes "i \<in> net_ips s"
    shows "fst (initmissing (netgmap sr s)) i = the (fst (netgmap sr s) i)"
  using assms unfolding initmissing_def by (clarsimp split: option.split)

lemma not_in_net_ips_fst_init_missing [simp]:
  assumes "i \<notin> net_ips s"
    shows "fst (initmissing (netgmap sr s)) i = someinit i"
  using assms unfolding initmissing_def by (clarsimp split: option.split)

lemma initmissing_oreachable_netmask [elim]:
  assumes "initmissing (netgmap sr s) \<in> oreachable (oclosed (opnet onp any)) (\<lambda>_ _ _. True) U"
          (is "_ \<in> ?oreachable any")
      and "net_ips s = net_tree_ips any"
    shows "netgmap sr s \<in> netmask (net_tree_ips any) ` ?oreachable any"
  proof -
    obtain \<sigma> \<zeta> where "initmissing (netgmap sr s) = (\<sigma>, \<zeta>)" by (metis surj_pair)
    with assms(1) have "(\<sigma>, \<zeta>) \<in> ?oreachable any" by simp

    have "netgmap sr s = netmask (net_ips s) (\<sigma>, \<zeta>)"
    proof (intro prod_eqI ext)
      fix i
      show "fst (netgmap sr s) i = fst (netmask (net_ips s) (\<sigma>, \<zeta>)) i"
      proof (cases "i\<in>net_ips s")
        assume "i\<in>net_ips s"
        hence "fst (initmissing (netgmap sr s)) i = the (fst (netgmap sr s) i)"
          by (rule in_net_ips_fst_init_missing)
        moreover from `i\<in>net_ips s` have "Some (the (fst (netgmap sr s) i)) = fst (netgmap sr s) i"
          by (rule some_the_fst_netgmap)
        ultimately show ?thesis
          using `initmissing (netgmap sr s) = (\<sigma>, \<zeta>)` by simp
      qed simp
    next
      from `initmissing (netgmap sr s) = (\<sigma>, \<zeta>)`
        show "snd (netgmap sr s) = snd (netmask (net_ips s) (\<sigma>, \<zeta>))"
          by simp
    qed
    with assms(2) have "netgmap sr s = netmask (net_tree_ips any) (\<sigma>, \<zeta>)" by simp
    moreover from `(\<sigma>, \<zeta>) \<in> ?oreachable any`
      have "netmask (net_ips s) (\<sigma>, \<zeta>) \<in> netmask (net_ips s) ` ?oreachable any"
        by (rule imageI)
    ultimately show ?thesis
      by (simp only: assms(2))
  qed

lemma pnet_reachable_transfer:
  assumes "wf_net_tree any"
      and "s \<in> reachable (closed (pnet np any)) TT"
    shows "initmissing (netgmap sr s) \<in> oreachable (oclosed (opnet onp any)) (\<lambda>_ _ _. True) U"
          (is " _ \<in> ?oreachable any")
  using assms(2) proof induction
    fix s
    assume "s \<in> init (closed (pnet np any))"
    hence "s \<in> init (pnet np any)" by simp

    from `wf_net_tree any` have "initmissing (netgmap sr s) \<in> init (opnet onp any)"
    proof (rule init_lifted [THEN set_mp], intro CollectI exI conjI allI)
      show "initmissing (netgmap sr s) = (fst (initmissing (netgmap sr s)), snd (netgmap sr s))"
        by (metis snd_initmissing surjective_pairing)
    next
      from `s \<in> init (pnet np any)` show "s \<in> init (pnet np any)" ..
    next
      fix i
      show "if i \<in> net_tree_ips any
            then (fst (initmissing (netgmap sr s))) i = the (fst (netgmap sr s) i)
            else (fst (initmissing (netgmap sr s))) i \<in> (fst \<circ> sr) ` init (np i)"
      proof (cases "i \<in> net_tree_ips any", simp_all only: if_True if_False)
        assume "i \<in> net_tree_ips any"
        with `s \<in> init (pnet np any)` have "i \<in> net_ips s" ..
        thus "fst (initmissing (netgmap sr s)) i = the (fst (netgmap sr s) i)" by simp
      next
        assume "i \<notin> net_tree_ips any"
        with `s \<in> init (pnet np any)` have "i \<notin> net_ips s" ..
        hence "fst (initmissing (netgmap sr s)) i = someinit i" by simp
        moreover have "someinit i \<in> (fst \<circ> sr) ` init (np i)"
        unfolding someinit_def proof (rule someI_ex)
          from init_notempty show "\<exists>x. x \<in> (fst o sr) ` init (np i)" by auto
        qed
        ultimately show "fst (initmissing (netgmap sr s)) i \<in> (fst \<circ> sr) ` init (np i)"
          by simp
      qed
    qed
    hence "initmissing (netgmap sr s) \<in> init (oclosed (opnet onp any))" by simp
    thus "initmissing (netgmap sr s) \<in> ?oreachable any" ..
  next
    fix s a s'
    assume "s \<in> reachable (closed (pnet np any)) TT"
       and "(s, a, s') \<in> trans (closed (pnet np any))"
       and "initmissing (netgmap sr s) \<in> ?oreachable any"
    from this(1) have "s \<in> reachable (pnet np any) TT" ..
    hence "net_ips s = net_tree_ips any" by (rule pnet_net_ips_net_tree_ips)
    with `initmissing (netgmap sr s) \<in> ?oreachable any`
      have "netgmap sr s \<in> netmask (net_tree_ips any) ` ?oreachable any"
        by (rule initmissing_oreachable_netmask)

    obtain \<sigma> \<zeta> where "(\<sigma>, \<zeta>) = initmissing (netgmap sr s)" by (metis surj_pair)
    with `initmissing (netgmap sr s) \<in> ?oreachable any`
      have "(\<sigma>, \<zeta>) \<in> ?oreachable any" by simp
    from `(\<sigma>, \<zeta>) = initmissing (netgmap sr s)` and `net_ips s = net_tree_ips any` [symmetric]
      have "netgmap sr s = netmask (net_tree_ips any) (\<sigma>, \<zeta>)"
        by (clarsimp simp add: netmask_initmissing_netgmap)

    with `s \<in> reachable (closed (pnet np any)) TT`
      obtain \<sigma>' \<zeta>' where "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp any))"
                     and "netgmap sr s' = netmask (net_tree_ips any) (\<sigma>', \<zeta>')"
        using `wf_net_tree any` and `(s, a, s') \<in> trans (closed (pnet np any))`
        by (rule transfer_action)

    from `(\<sigma>, \<zeta>) \<in> ?oreachable any` have "net_ips \<zeta> = net_tree_ips any"
      by (rule opnet_net_ips_net_tree_ips [OF oclosed_oreachable_oreachable])
    with `((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp any))`
      have "\<forall>j. j\<notin>net_tree_ips any \<longrightarrow> \<sigma>' j = \<sigma> j"
        by (clarsimp elim!: ocomplete_no_change)
    have "initmissing (netgmap sr s') = (\<sigma>', \<zeta>')"
    proof (intro prod_eqI ext)
      fix i
      from `netgmap sr s' = netmask (net_tree_ips any) (\<sigma>', \<zeta>')`
           `\<forall>j. j\<notin>net_tree_ips any \<longrightarrow> \<sigma>' j = \<sigma> j`
           `(\<sigma>, \<zeta>) = initmissing (netgmap sr s)`
           `net_ips s = net_tree_ips any`
      show "fst (initmissing (netgmap sr s')) i = fst (\<sigma>', \<zeta>') i"
        unfolding initmissing_def by simp
    next
      from `netgmap sr s' = netmask (net_tree_ips any) (\<sigma>', \<zeta>')`
        show "snd (initmissing (netgmap sr s')) = snd (\<sigma>', \<zeta>')" by simp
    qed
    moreover from `(\<sigma>, \<zeta>) \<in> ?oreachable any` `((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet onp any))`
      have "(\<sigma>', \<zeta>') \<in> ?oreachable any"
        by (rule oreachable_local) (rule TrueI)

    ultimately show "initmissing (netgmap sr s') \<in> ?oreachable any"
      by simp
  qed

definition
  netglobal :: "((nat \<Rightarrow> 'g) \<Rightarrow> bool) \<Rightarrow> 's net_state \<Rightarrow> bool"
where
  "netglobal P \<equiv> (\<lambda>s. P (fst (initmissing (netgmap sr s))))"

lemma netglobalsimp [simp]:
  "netglobal P s = P (fst (initmissing (netgmap sr s)))"
  unfolding netglobal_def by simp

lemma netglobalE [elim]:
  assumes "netglobal P s"
      and "\<And>\<sigma>. \<lbrakk> P \<sigma>; fst (initmissing (netgmap sr s)) = \<sigma> \<rbrakk> \<Longrightarrow> Q \<sigma>"
    shows "netglobal Q s"
  using assms by simp

lemma netglobal_weakenE [elim]:
  assumes "p \<TTurnstile> netglobal P"
      and "\<And>\<sigma>. P \<sigma> \<Longrightarrow> Q \<sigma>"
    shows "p \<TTurnstile> netglobal Q"
  using assms(1) proof (rule invariant_weakenE)
    fix s
    assume "netglobal P s"
    thus "netglobal Q s"
      by (rule netglobalE) (erule assms(2))
  qed

lemma close_opnet:
  assumes "wf_net_tree any"
      and "oclosed (opnet onp any) \<Turnstile> (\<lambda>_ _ _. True, U \<rightarrow>) global P"
    shows "closed (pnet np any) \<TTurnstile> netglobal P"
  unfolding invariant_def proof
    fix s
    assume "s \<in> reachable (closed (pnet np any)) TT"
    with assms(1)
      have "initmissing (netgmap sr s) \<in> oreachable (oclosed (opnet onp any)) (\<lambda>_ _ _. True) U"
        by (rule pnet_reachable_transfer)
    with assms(2) have "global P (initmissing (netgmap sr s))" ..
    thus "netglobal P s" by simp
  qed

end

locale openproc_parq =
  op: openproc np onp sr for np :: "ip \<Rightarrow> ('s, ('m::msg) seq_action) automaton" and onp sr
  + fixes qp :: "('t, 'm seq_action) automaton"
    assumes init_qp_notempty: "init qp \<noteq> {}"

sublocale openproc_parq \<subseteq> openproc "\<lambda>i. np i \<langle>\<langle> qp"
                                   "\<lambda>i. onp i \<langle>\<langle>\<^bsub>i\<^esub> qp"
                                   "\<lambda>(p, q). (fst (sr p), (snd (sr p), q))"
  proof unfold_locales
    fix i
    show "{ (\<sigma>, \<zeta>) |\<sigma> \<zeta> s. s \<in> init (np i \<langle>\<langle> qp)
                         \<and> (\<sigma> i, \<zeta>) = ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s)
                         \<and> (\<forall>j. j\<noteq>i \<longrightarrow> \<sigma> j \<in> (fst o (\<lambda>(p, q). (fst (sr p), (snd (sr p), q))))
                                                  ` init (np j \<langle>\<langle> qp)) } \<subseteq> init (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
       (is "?S \<subseteq> _")
    proof
      fix s
      assume "s \<in> ?S"
      then obtain \<sigma> p lq
        where "s = (\<sigma>, (snd (sr p), lq))"
          and "lq \<in> init qp"
          and "p \<in> init (np i)"
          and "\<sigma> i = fst (sr p)"
          and "\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j \<in> (fst \<circ> (\<lambda>(p, q). (fst (sr p), snd (sr p), q)))
                                                                        ` (init (np j) \<times> init qp)"
        by auto
      from this(5) have "\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j \<in> (fst \<circ> sr) ` init (np j)"
        by auto
      with `p \<in> init (np i)` and `\<sigma> i = fst (sr p)` have "(\<sigma>, snd (sr p)) \<in> init (onp i)"
        by - (rule init [THEN set_mp], auto)
      with `lq\<in> init qp` have "((\<sigma>, snd (sr p)), lq) \<in> init (onp i) \<times> init qp"
        by simp
      hence "(\<sigma>, (snd (sr p), lq)) \<in> extg ` (init (onp i) \<times> init qp)"
        by (rule rev_image_eqI) simp
      with `s = (\<sigma>, (snd (sr p), lq))` show "s \<in> init (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
        by simp
    qed
  next
    fix i s a s' \<sigma> \<sigma>'
    assume "\<sigma> i = fst ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s)"
       and "\<sigma>' i = fst ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s')"
       and "(s, a, s') \<in> trans (np i \<langle>\<langle> qp)"
    then obtain p q p' q' where "s  = (p, q)"
                            and "s' = (p', q')"
                            and "\<sigma> i  = fst (sr p)"
                            and "\<sigma>' i = fst (sr p')"
      by (clarsimp split: split_split_asm)
    from this(1-2) and `(s, a, s') \<in> trans (np i \<langle>\<langle> qp)`
      have "((p, q), a, (p', q')) \<in> parp_sos (trans (np i)) (trans qp)" by simp
    hence "((\<sigma>, (snd (sr p), q)), a, (\<sigma>', (snd (sr p'), q'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
    proof cases
      assume "q' = q"
         and "(p, a, p') \<in> trans (np i)"
         and "\<And>m. a \<noteq> receive m"
      from `\<sigma> i = fst (sr p)` and `\<sigma>' i = fst (sr p')` this(2)
        have "((\<sigma>, snd (sr p)), a, (\<sigma>', snd (sr p'))) \<in> trans (onp i)" by (rule trans)
      with `q' = q` and `\<And>m. a \<noteq> receive m`
        show "((\<sigma>, snd (sr p), q), a, (\<sigma>', (snd (sr p'), q'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
          by (auto elim!: oparleft)
    next
      assume "p' = p"
         and "(q, a, q') \<in> trans qp"
         and "\<And>m. a \<noteq> send m"
      with `\<sigma> i = fst (sr p)` and `\<sigma>' i = fst (sr p')`
        show "((\<sigma>, snd (sr p), q), a, (\<sigma>', (snd (sr p'), q'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
          by (auto elim!: oparright)
    next
      fix m
      assume "a = \<tau>"
         and "(p, receive m, p') \<in> trans (np i)"
         and "(q, send m, q') \<in> trans qp"
      from `\<sigma> i = fst (sr p)` and `\<sigma>' i = fst (sr p')` this(2)
        have "((\<sigma>, snd (sr p)), receive m, (\<sigma>', snd (sr p'))) \<in> trans (onp i)"
          by (rule trans)
      with `(q, send m, q') \<in> trans qp` and `a = \<tau>`
        show "((\<sigma>, snd (sr p), q), a, (\<sigma>', (snd (sr p'), q'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
          by (simp del: step_seq_tau) (rule oparboth)
    qed
    with `s = (p, q)` `s' = (p', q')`
      show "((\<sigma>, snd ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s)), a,
                 (\<sigma>', snd ((\<lambda>(p, q). (fst (sr p), (snd (sr p), q))) s'))) \<in> trans (onp i \<langle>\<langle>\<^bsub>i\<^esub> qp)"
        by simp
  next
    show "\<forall>j. init (np j \<langle>\<langle> qp) \<noteq> {}"
      by (clarsimp simp add: init_notempty init_qp_notempty)
  qed

end
