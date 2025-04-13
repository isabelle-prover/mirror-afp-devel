section \<open>Critical Pairs\<close>

theory Critical_Pairs
  imports
    Trs
    First_Order_Terms.Unification
begin

text\<open>We also consider overlaps between the same rule at top level,
   in this way we are not restricted to @{const wf_trs}.\<close>
context
  fixes ren :: "'v :: infinite renaming2"  (* fix some renaming scheme *)
begin

definition
  critical_Peaks :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> ((('f, 'v)term \<times> ('f,'v)term \<times> ('f,'v)term)) set"
  where
    "critical_Peaks P R = { ((C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, l \<cdot> \<sigma>, r \<cdot> \<sigma>) | l r l' r' l'' C \<sigma> \<tau>.
    (l, r) \<in> P \<and> (l', r') \<in> R \<and> l = C\<langle>l''\<rangle> \<and> is_Fun l'' \<and>
    mgu_vd ren l'' l' = Some (\<sigma>, \<tau>) }"

definition
  critical_pairs :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> (bool \<times> ('f, 'v) rule) set"
  where
    "critical_pairs P R = { (C = \<box>, (C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>, r \<cdot> \<sigma>) | l r l' r' l'' C \<sigma> \<tau>.
    (l, r) \<in> P \<and> (l', r') \<in> R \<and> l = C\<langle>l''\<rangle> \<and> is_Fun l'' \<and>
    mgu_vd ren l'' l' = Some (\<sigma>, \<tau>) }"

lemma critical_pairsI:
  assumes "(l, r) \<in> P" and "(l', r') \<in> R" and "l = C\<langle>l''\<rangle>"
    and "is_Fun l''" and "mgu_vd ren l'' l' = Some (\<sigma>, \<tau>)" and "t = r \<cdot> \<sigma>"
    and "s = (C \<cdot>\<^sub>c \<sigma>)\<langle>r' \<cdot> \<tau>\<rangle>" and "b = (C = \<box>)"
  shows "(b, s, t) \<in> critical_pairs P R"
  using assms unfolding critical_pairs_def by blast

lemma critical_pairs_mono:
  assumes "S\<^sub>1 \<subseteq> R\<^sub>1" and "S\<^sub>2 \<subseteq> R\<^sub>2" shows "critical_pairs S\<^sub>1 S\<^sub>2 \<subseteq> critical_pairs R\<^sub>1 R\<^sub>2"
  unfolding critical_pairs_def using assms by blast

lemma critical_Peaks_main:
  fixes P R :: "('f, 'v) trs"
  assumes tu: "(t, u) \<in> rrstep P" and ts: "(t, s) \<in> rstep R"
  shows "(s, u) \<in> (rstep R)^* O rrstep P O ((rstep R)^*)^-1 \<or>
    (\<exists> C l m r \<sigma>. s = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>m \<cdot> \<sigma>\<rangle> \<and> u = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> 
    (l, m, r) \<in> critical_Peaks P R)"
proof -
  let ?R = "rstep R"
  let ?CP = "critical_Peaks P R"
  from rrstepE[OF tu] obtain l1 r1 \<sigma>1 where lr1: "(l1, r1) \<in> P" and t1: "t = l1 \<cdot> \<sigma>1" and u: "u = r1 \<cdot> \<sigma>1" by auto
  from ts obtain C l2 r2 \<sigma>2 where lr2: "(l2, r2) \<in> R" and t2: "t = C\<langle>l2 \<cdot> \<sigma>2\<rangle>" and s: "s = C\<langle>r2 \<cdot> \<sigma>2\<rangle>" by auto
  from t1 t2 have id: "l1 \<cdot> \<sigma>1 = C\<langle>l2 \<cdot> \<sigma>2\<rangle>" by auto
  let ?p = "hole_pos C"
  show ?thesis
  proof (cases "?p \<in> poss l1 \<and> is_Fun (l1 |_ ?p)")
    case True
    then have p: "?p \<in> poss l1" by auto
    from ctxt_supt_id [OF p] obtain D where Dl1: "D\<langle>l1 |_ ?p\<rangle> = l1"
      and D: "D = ctxt_of_pos_term (hole_pos C) l1" by blast
    from arg_cong [OF Dl1, of "\<lambda> t. t \<cdot> \<sigma>1"]
    have "(D \<cdot>\<^sub>c \<sigma>1)\<langle>(l1 |_ ?p) \<cdot> \<sigma>1\<rangle> = C\<langle>l2 \<cdot> \<sigma>2\<rangle>" unfolding id by simp
    from arg_cong [OF this, of "\<lambda> t. t |_ ?p"]
    have "l2 \<cdot> \<sigma>2 = (D \<cdot>\<^sub>c \<sigma>1)\<langle>(l1 |_ ?p) \<cdot> \<sigma>1\<rangle> |_ ?p" by simp
    also have "... = (D \<cdot>\<^sub>c \<sigma>1)\<langle>(l1 |_ ?p) \<cdot> \<sigma>1\<rangle> |_ (hole_pos (D \<cdot>\<^sub>c \<sigma>1))"
      using hole_pos_ctxt_of_pos_term [OF p] unfolding D by simp
    also have "... = (l1 |_ ?p) \<cdot> \<sigma>1" by (rule subt_at_hole_pos)
    finally have ident: "l2 \<cdot> \<sigma>2 = l1 |_ ?p \<cdot> \<sigma>1" by auto
    from mgu_vd_complete [OF ident [symmetric]]
    obtain \<mu>1 \<mu>2 \<rho> where mgu: "mgu_vd ren (l1 |_ ?p) l2 = Some (\<mu>1, \<mu>2)" and
      \<mu>1: "\<sigma>1 = \<mu>1 \<circ>\<^sub>s \<rho>"
      and \<mu>2: "\<sigma>2 = \<mu>2 \<circ>\<^sub>s \<rho>"
      and ident': "l1 |_ ?p \<cdot> \<mu>1 = l2 \<cdot> \<mu>2" by blast
    have in_cp: "((D \<cdot>\<^sub>c \<mu>1)\<langle>r2 \<cdot> \<mu>2\<rangle>, l1 \<cdot> \<mu>1, r1 \<cdot> \<mu>1) \<in> ?CP"
      unfolding critical_Peaks_def
      apply clarify
      apply (intro exI conjI)
           apply (rule refl)
          apply (rule lr1)
         apply (rule lr2)
        apply (rule Dl1[symmetric])
       apply (rule True[THEN conjunct2])
      apply (rule mgu)
      done
    from hole_pos_ctxt_of_pos_term [OF p] D have pD: "?p = hole_pos D" by simp
    from id have C: "C = ctxt_of_pos_term ?p (l1 \<cdot> \<sigma>1)" by simp
    have "C\<langle>r2 \<cdot> \<sigma>2\<rangle> = (ctxt_of_pos_term ?p (l1 \<cdot> \<sigma>1))\<langle>r2 \<cdot> \<sigma>2\<rangle>" using C by simp
    also have "... = (ctxt_of_pos_term ?p l1 \<cdot>\<^sub>c \<sigma>1)\<langle>r2 \<cdot> \<sigma>2\<rangle>" unfolding ctxt_of_pos_term_subst [OF p] ..
    also have "... = (D \<cdot>\<^sub>c \<sigma>1)\<langle>r2 \<cdot> \<sigma>2\<rangle>" unfolding D ..
    finally have Cr\<sigma>: "C\<langle>r2 \<cdot> \<sigma>2\<rangle> = (D \<cdot>\<^sub>c \<sigma>1)\<langle>r2 \<cdot> \<sigma>2\<rangle>" .
    show ?thesis unfolding Cr\<sigma> s u t1 unfolding \<mu>1 \<mu>2
    proof (rule disjI2, intro exI, intro conjI)
      show "r1 \<cdot> \<mu>1 \<circ>\<^sub>s \<rho> = \<box>\<langle>r1 \<cdot> \<mu>1 \<cdot> \<rho>\<rangle>" by simp
    qed (insert in_cp, auto)
  next
    case False
    from pos_into_subst [OF id _ False]
    obtain q q' x where p: "?p = q @ q'" and q: "q \<in> poss l1" and l1q: "l1 |_ q = Var x" by auto
    have "l2 \<cdot> \<sigma>2 = C\<langle>l2 \<cdot> \<sigma>2\<rangle> |_ (q @ q')" unfolding p [symmetric] by simp
    also have "... = l1 \<cdot> \<sigma>1 |_ (q @ q')" unfolding id ..
    also have "... = l1 |_ q \<cdot> \<sigma>1 |_ q'" using q by simp
    also have "... = \<sigma>1 x |_ q'" unfolding l1q by simp
    finally have l2x: "l2 \<cdot> \<sigma>2 = \<sigma>1 x |_ q'" by simp
    have pp: "?p \<in> poss (l1 \<cdot> \<sigma>1)" unfolding id by simp
    then have "q @ q' \<in> poss (l1 \<cdot> \<sigma>1)" unfolding p .
    then have "q' \<in> poss (l1 \<cdot> \<sigma>1 |_ q)" unfolding poss_append_poss ..
    with q have "q' \<in> poss (l1 |_ q \<cdot> \<sigma>1)" by auto
    then have q'x: "q' \<in> poss (\<sigma>1 x)" unfolding l1q by simp
    from ctxt_supt_id [OF q'x] obtain E where \<sigma>1x: "E\<langle>l2 \<cdot> \<sigma>2\<rangle> = \<sigma>1 x"
      and E: "E = ctxt_of_pos_term q' (\<sigma>1 x)"
      unfolding l2x by blast
    let ?e = "E\<langle>r2 \<cdot> \<sigma>2\<rangle>"
    from hole_pos_ctxt_of_pos_term [OF q'x] E have q': "q' = hole_pos E" by simp
    from \<sigma>1x have \<sigma>1x': "\<sigma>1 x = E\<langle>l2 \<cdot> \<sigma>2\<rangle>" by simp
    let ?\<sigma> = "\<lambda> y. if y = x then ?e else \<sigma>1 y"
    have "(u, r1 \<cdot> ?\<sigma>) \<in> (rstep R)^*" unfolding u
    proof (rule subst_rsteps_imp_rsteps)
      fix y
      show "(\<sigma>1 y, ?\<sigma> y) \<in> (rstep R)^*"
      proof (cases "y = x")
        case True
        show ?thesis unfolding True \<sigma>1x' using lr2 by auto
      qed simp
    qed
    hence r1u: "(r1 \<cdot> ?\<sigma>, u) \<in> ((rstep R)^*)^-1" by auto
    show ?thesis
    proof (rule disjI1, intro relcompI)
      show "(r1 \<cdot> ?\<sigma>, u) \<in> ((rstep R)^*)^-1" by fact
      show "(l1 \<cdot> ?\<sigma>, r1 \<cdot> ?\<sigma>) \<in> rrstep P" using lr1 by auto
      from q have ql1:  "q \<in> poss (l1 \<cdot> \<sigma>1)" by simp
      have "s = replace_at (C\<langle>l2 \<cdot> \<sigma>2\<rangle>) ?p (r2 \<cdot> \<sigma>2)" unfolding s by simp
      also have "... = replace_at (l1 \<cdot> \<sigma>1) ?p (r2 \<cdot> \<sigma>2)" unfolding id ..
      also have "... = replace_at (l1 \<cdot> \<sigma>1) q ?e"
      proof -
        have "E = ctxt_of_pos_term q' (l1 \<cdot> \<sigma>1 |_ q)"
          unfolding subt_at_subst [OF q] l1q E by simp
        then show ?thesis
          unfolding p
          unfolding ctxt_of_pos_term_append [OF ql1]
          by simp
      qed
      finally have s: "s = replace_at (l1 \<cdot> \<sigma>1) q ?e" .
      from q l1q have "(replace_at (l1 \<cdot> \<sigma>1) q ?e, l1 \<cdot> ?\<sigma>) \<in> ?R^*"
      proof (induct l1 arbitrary: q)
        case (Fun f ls)
        from Fun(2, 3) obtain i p where q: "q = i # p" and i: "i < length ls" and p: "p \<in> poss (ls ! i)" and px: "ls ! i |_ p = Var x" by (cases q, auto)
        from i have "ls ! i \<in> set ls" by auto
        from Fun(1) [OF this p px] have rec: "(replace_at (ls ! i \<cdot> \<sigma>1) p ?e, ls ! i \<cdot> ?\<sigma>) \<in> ?R^*" .
        let ?ls\<sigma> = "map (\<lambda> t. t \<cdot> \<sigma>1) ls"
        let ?ls\<sigma>' = "map (\<lambda> t. t \<cdot> ?\<sigma>) ls"
        have id: "replace_at (Fun f ls \<cdot> \<sigma>1) q ?e = Fun f (take i ?ls\<sigma> @ replace_at (ls ! i \<cdot> \<sigma>1) p ?e # drop (Suc i) ?ls\<sigma>)" (is "_ = Fun f ?r")
          unfolding q using i by simp
        show ?case unfolding id unfolding eval_term.simps
        proof (rule all_ctxt_closedD [of UNIV])
          fix j
          assume j: "j < length ?r"
          show "(?r ! j, ?ls\<sigma>' ! j) \<in> ?R^*"
          proof (cases "j = i")
            case True
            show ?thesis using i True using rec by (auto simp: nth_append)
          next
            case False
            have "?r ! j = ?ls\<sigma> ! j"
              by (rule nth_append_take_drop_is_nth_conv, insert False i j, auto)
            also have "... = ls ! j \<cdot> \<sigma>1" using j i by auto
            finally have idr: "?r ! j = ls ! j \<cdot> \<sigma>1" .
            from j i have idl: "?ls\<sigma>' ! j = ls ! j \<cdot> ?\<sigma>" by auto
            show ?thesis unfolding idr idl
            proof (rule subst_rsteps_imp_rsteps)
              fix y
              show "(\<sigma>1 y, ?\<sigma> y) \<in> ?R^*"
              proof (cases "y = x")
                case True then show ?thesis using \<sigma>1x' lr2 by auto
              qed simp
            qed
          qed
        qed (insert i, auto)
      qed simp
      then show "(s, l1 \<cdot> ?\<sigma>) \<in> ?R^*" unfolding s .
    qed
  qed
qed

lemma critical_Peaks_main_rrstep:
  fixes R :: "('f, 'v) trs"
  assumes tu: "(t, u) \<in> rrstep R" and ts: "(t, s) \<in> rstep R"
  shows "(s, u) \<in> join (rstep R) \<or>
    (\<exists> C l m r \<sigma>. s = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>m \<cdot> \<sigma>\<rangle> \<and> u = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> 
    (l, m, r) \<in> critical_Peaks R R)"
  using critical_Peaks_main[OF assms] 
proof
  assume "(s, u) \<in> (rstep R)\<^sup>* O rrstep R O ((rstep R)\<^sup>*)\<inverse>" 
  also have "\<dots> \<subseteq> (rstep R)\<^sup>* O ((rstep R)\<^sup>*)\<inverse>" 
    unfolding rstep_iff_rrstep_or_nrrstep by regexp
  finally have "(s, u) \<in> join (rstep R)" by blast
  thus ?thesis by auto
qed auto

lemma parallel_rstep:
  fixes p1 :: pos
  assumes p12: "p1 \<bottom> p2"
    and p1: "p1 \<in> poss t"
    and p2: "p2 \<in> poss t"
    and step2: "t |_ p2 = l2 \<cdot> \<sigma>2" "(l2,r2) \<in> R" 
  shows "(replace_at t p1 v, replace_at (replace_at t p1 v) p2 (r2 \<cdot> \<sigma>2)) \<in> rstep R" (is "(?one,?two) \<in> _")
proof -
  show ?thesis unfolding rstep_iff_rstep_r_p_s
  proof (intro exI)
    show "(?one,?two) \<in> rstep_r_p_s R (l2,r2) p2 \<sigma>2"
      unfolding rstep_r_p_s_def Let_def
      apply (intro CollectI, unfold split fst_conv snd_conv)
      using p1 p12 p2 step2
      by (metis ctxt_supt_id parallel_poss_replace_at parallel_replace_at_subt_at)
  qed
qed

lemma critical_Peaks_main_rstep:
  fixes R :: "('f, 'v) trs"
  assumes tu: "(t, u) \<in> rstep R" and ts: "(t, s) \<in> rstep R"
  shows "(s, u) \<in> join (rstep R) \<or>
    (\<exists> C l m r \<sigma>. s = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>m \<cdot> \<sigma>\<rangle> \<and> u = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> 
    ((l, m, r) \<in> critical_Peaks R R \<or> (r, m, l) \<in> critical_Peaks R R))"
proof - 
  let ?R = "rstep R"
  let ?CP = "critical_Peaks R R"
  from tu obtain C1 l1 r1 \<sigma>1 where lr1: "(l1, r1) \<in> R" and t1: "t = C1\<langle>l1 \<cdot> \<sigma>1\<rangle>" and u: "u = C1\<langle>r1 \<cdot> \<sigma>1\<rangle>" by auto
  from ts obtain C2 l2 r2 \<sigma>2 where lr2: "(l2, r2) \<in> R" and t2: "t = C2\<langle>l2 \<cdot> \<sigma>2\<rangle>" and s: "s = C2\<langle>r2 \<cdot> \<sigma>2\<rangle>" by auto
  define n where "n = size C1 + size C2" 
  from t1 t2 u s n_def show ?thesis
  proof (induct n arbitrary: C1 C2 s t u rule: less_induct)
    case (less n C1 C2 s t u)
    show ?case
    proof (cases C1)
      case Hole
      with less(2,4) lr1 have tu: "(t, u) \<in> rrstep R" by auto
      from less(3,5) lr2 have ts: "(t, s) \<in> rstep R" by auto
      from critical_Peaks_main_rrstep[OF tu ts] show ?thesis by auto
    next
      case (More f1 bef1 D1 aft1) note C1 = this
      show ?thesis
      proof (cases C2)
        case Hole 
        with less(3,5) lr2 have ts: "(t, s) \<in> rrstep R" by auto
        from less(2,4) lr1 have tu: "(t, u) \<in> rstep R" by auto
        from critical_Peaks_main_rrstep[OF ts tu] show ?thesis by auto
      next
        case (More f2 bef2 D2 aft2) note C2 = this
        from less(2-3) C1 C2 
        have id: "(More f1 bef1 D1 aft1)\<langle>l1 \<cdot> \<sigma>1\<rangle> = (More f2 bef2 D2 aft2)\<langle>l2 \<cdot> \<sigma>2\<rangle>" by auto
        let ?n1 = "length bef1"
        let ?n2 = "length bef2"
        from id have f: "f1 = f2" by simp
        show ?thesis
        proof (cases "?n1 = ?n2")
          case True
          with id have idb: "bef1 = bef2" and ida: "aft1 = aft2"
            and idD: "D1\<langle>l1 \<cdot> \<sigma>1\<rangle> = D2\<langle>l2 \<cdot> \<sigma>2\<rangle>" by auto
          let ?C = "More f2 bef2 \<box> aft2"
          have id1: "C1 = ?C \<circ>\<^sub>c D1" unfolding C1 f ida idb by simp
          have id2: "C2 = ?C \<circ>\<^sub>c D2" unfolding C2 by simp
          define m where "m = size D1 + size D2" 
          have mn: "m < n" unfolding less m_def C1 C2 by auto
          note IH = less(1)[OF mn refl idD refl refl m_def]
          then show ?thesis
          proof
            assume "( D2\<langle>r2 \<cdot> \<sigma>2\<rangle>, D1\<langle>r1 \<cdot> \<sigma>1\<rangle>) \<in> join ?R"
            then obtain s' where seq1: "(D1\<langle>r1 \<cdot> \<sigma>1\<rangle>, s') \<in> ?R^*"
              and seq2: "(D2\<langle>r2 \<cdot> \<sigma>2\<rangle>, s') \<in> ?R^*" by auto
            from rsteps_closed_ctxt [OF seq1, of ?C]
            have seq1: "(C1\<langle>r1 \<cdot> \<sigma>1\<rangle>, ?C\<langle>s'\<rangle>) \<in> ?R^*" using id1 by auto
            from rsteps_closed_ctxt [OF seq2, of ?C]
            have seq2: "(C2\<langle>r2 \<cdot> \<sigma>2\<rangle>, ?C\<langle>s'\<rangle>) \<in> ?R^*" using id2 by auto
            from seq1 seq2 show ?thesis using less by auto
          next
            assume "\<exists>C l m r \<sigma>. D2\<langle>r2 \<cdot> \<sigma>2\<rangle> = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> D1\<langle>l1 \<cdot> \<sigma>1\<rangle> = C\<langle>m \<cdot> \<sigma>\<rangle> \<and> D1\<langle>r1 \<cdot> \<sigma>1\<rangle> = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> ((l, m, r) \<in> ?CP \<or> (r, m, l) \<in> ?CP)"
            then obtain C l m r \<sigma> where idD: "D2\<langle>r2 \<cdot> \<sigma>2\<rangle> = C\<langle>l \<cdot> \<sigma>\<rangle>" "D1\<langle>l1 \<cdot> \<sigma>1\<rangle> = C\<langle>m \<cdot> \<sigma>\<rangle>" "D1\<langle>r1 \<cdot> \<sigma>1\<rangle> = C\<langle>r \<cdot> \<sigma>\<rangle>" and mem: "((l, m, r) \<in> ?CP \<or> (r, m, l) \<in> ?CP)" by blast
            show ?thesis
              apply (intro disjI2)
              apply (unfold less id1 id2)
              apply (intro exI [of _ "?C \<circ>\<^sub>c C"] exI)
              by (rule conjI [OF _ conjI [OF _ conjI[OF _ mem]]], insert idD, auto)
          qed
        next
          case False
          let ?p1 = "?n1 # hole_pos D1"
          let ?p2 = "?n2 # hole_pos D2"
          have l2: "C1\<langle>l1 \<cdot> \<sigma>1\<rangle> |_ ?p2 = l2 \<cdot> \<sigma>2" unfolding C1 id by simp
          have p12: "?p1  \<bottom> ?p2" using False by simp
          have p1: "?p1 \<in> poss (C1\<langle>l1 \<cdot> \<sigma>1\<rangle>)" unfolding C1 by simp
          have p2: "?p2 \<in> poss (C1\<langle>l1 \<cdot> \<sigma>1\<rangle>)" unfolding C1 unfolding id by simp
          let ?one = "replace_at (C1\<langle>l1 \<cdot> \<sigma>1\<rangle>) ?p1 (r1 \<cdot> \<sigma>1)"
          have one: "C1\<langle>r1 \<cdot> \<sigma>1\<rangle> = ?one" unfolding C1 by simp
          from parallel_rstep [OF p12 p1 p2 l2 lr2, of "r1 \<cdot> \<sigma>1"]
          have "(?one, replace_at ?one ?p2 (r2 \<cdot> \<sigma>2)) \<in> rstep R" by auto
          then have one: "(C1\<langle>r1 \<cdot> \<sigma>1\<rangle>, replace_at ?one ?p2 (r2 \<cdot> \<sigma>2)) \<in> (rstep R)^*" unfolding one by simp
          have l1: "C2\<langle>l2 \<cdot> \<sigma>2\<rangle> |_ ?p1 = l1 \<cdot> \<sigma>1" unfolding C2 id [symmetric] by simp
          have p21: "?p2  \<bottom> ?p1" using False by simp
          have p1': "?p1 \<in> poss (C2\<langle>l2 \<cdot> \<sigma>2\<rangle>)" unfolding C2 id [symmetric] by simp
          have p2': "?p2 \<in> poss (C2\<langle>l2 \<cdot> \<sigma>2\<rangle>)" unfolding C2 by simp
          let ?two = "replace_at (C2\<langle>l2 \<cdot> \<sigma>2\<rangle>) ?p2 (r2 \<cdot> \<sigma>2)"
          have two: "C2\<langle>r2 \<cdot> \<sigma>2\<rangle> = ?two" unfolding C2 by simp
          from parallel_rstep [OF p21 p2' p1' l1 lr1, of "r2 \<cdot> \<sigma>2"]
          have "(?two, replace_at ?two ?p1 (r1 \<cdot> \<sigma>1)) \<in> rstep R" by auto
          then have two: "(C2\<langle>r2 \<cdot> \<sigma>2\<rangle>, replace_at ?two ?p1 (r1 \<cdot> \<sigma>1)) \<in> (rstep R)^*" unfolding two by simp
          have "replace_at ?one ?p2 (r2 \<cdot> \<sigma>2) = replace_at (replace_at (C1\<langle>l1 \<cdot> \<sigma>1\<rangle>) ?p2 (r2 \<cdot> \<sigma>2)) ?p1 (r1 \<cdot> \<sigma>1)"
            by (rule parallel_replace_at [OF p12 p1 p2])
          also have "... = replace_at ?two ?p1 (r1 \<cdot> \<sigma>1)" unfolding C1 C2 id ..
          finally have one_two: "replace_at ?one ?p2 (r2 \<cdot> \<sigma>2) = replace_at ?two ?p1 (r1 \<cdot> \<sigma>1)" .
          show ?thesis unfolding less
            by (rule disjI1, insert one one_two two, auto)
        qed
      qed
    qed
  qed
qed

lemma critical_Peak_steps:
  fixes R :: "('f, 'v) trs" and S
  assumes cp: "(l, m, r) \<in> critical_Peaks R S"
  shows "(m, l) \<in> rstep S" "(m,r) \<in> rstep R" "(m,r) \<in> rrstep R" 
proof -
  from cp [unfolded critical_Peaks_def]
  obtain \<sigma>1 \<sigma>2 l1 l2 r1 r2 C where id: "r = r1 \<cdot> \<sigma>1" "l = (C \<cdot>\<^sub>c \<sigma>1)\<langle>r2 \<cdot> \<sigma>2\<rangle>" "m = (C \<cdot>\<^sub>c \<sigma>1)\<langle>l1 \<cdot> \<sigma>1\<rangle>" 
    and r1: "(C\<langle>l1\<rangle>, r1) \<in> R" and r2: "(l2, r2) \<in> S" and mgu: "mgu_vd ren l1 l2 = Some (\<sigma>1, \<sigma>2)" by auto
  have "(C\<langle>l1\<rangle> \<cdot> \<sigma>1, r) \<in> rrstep R" unfolding id
    by (rule rrstepI [of "C\<langle>l1\<rangle>" r1 _ _ \<sigma>1] r1, insert r1, auto)
  thus "(m,r) \<in> rrstep R" unfolding id by auto
  thus "(m,r) \<in> rstep R" by (rule rrstep_imp_rstep)
  from mgu_vd_sound [OF mgu] have change: "C\<langle>l1\<rangle> \<cdot> \<sigma>1 = (C \<cdot>\<^sub>c \<sigma>1)\<langle>l2 \<cdot> \<sigma>2\<rangle>" by simp
  have "(C\<langle>l1\<rangle> \<cdot> \<sigma>1, l) \<in> rstep S" unfolding change id
    by (rule rstepI [OF r2, of _ _ \<sigma>2], auto)
  thus "(m, l) \<in> rstep S" unfolding id by auto
qed

lemma critical_Peak_to_pair: assumes "(l, m, r) \<in> critical_Peaks R R" 
  shows "\<exists> b. (b, l, r) \<in> critical_pairs R R" 
  using assms unfolding critical_Peaks_def critical_pairs_def by blast


lemma critical_pairs_main:
  fixes R :: "('f, 'v) trs"
  assumes st1: "(s, t1) \<in> rstep R" and st2: "(s, t2) \<in> rstep R"
  shows "(t1, t2) \<in> join (rstep R) \<or>
    (\<exists> C b l r \<sigma>. t1 = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t2 = C\<langle>r \<cdot> \<sigma>\<rangle> \<and>
    ((b, l, r) \<in> critical_pairs R R \<or> (b, r, l) \<in> critical_pairs R R))"
  using critical_Peaks_main_rstep[OF st2 st1]
proof 
  assume "\<exists>C l m r \<sigma>.
       t1 = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> s = C\<langle>m \<cdot> \<sigma>\<rangle> \<and> t2 = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> ((l, m, r) \<in> critical_Peaks R R \<or> (r, m, l) \<in> critical_Peaks R R)" 
  then obtain C l m r \<sigma> where id: "t1 = C\<langle>l \<cdot> \<sigma>\<rangle>" "t2 = C\<langle>r \<cdot> \<sigma>\<rangle>" and disj: "((l, m, r) \<in> critical_Peaks R R \<or> (r, m, l) \<in> critical_Peaks R R)" 
    by blast
  from critical_Peak_to_pair disj obtain b where "(b,l,r) \<in> critical_pairs R R \<or> (b,r,l) \<in> critical_pairs R R" by blast
  with id show ?thesis by blast
qed auto

lemma critical_pairs:
  fixes R :: "('f, 'v) trs"
  assumes cp: "\<And> l r b. (b, l, r) \<in> critical_pairs R R \<Longrightarrow> l \<noteq> r \<Longrightarrow>
    \<exists> l' r' s. instance_rule (l, r) (l', r') \<and> (l', s) \<in> (rstep R)\<^sup>* \<and> (r', s) \<in> (rstep R)\<^sup>*"
  shows "WCR (rstep R)"
proof
  let ?R = "rstep R"
  let ?CP = "critical_pairs R R"
  fix s t1 t2
  assume steps: "(s, t1) \<in> ?R" "(s, t2) \<in> ?R"
  let ?p = "\<lambda> s'. (t1, s') \<in> ?R^* \<and> (t2, s') \<in> ?R^*"
  from critical_pairs_main [OF steps]
  have "\<exists> s'. ?p s'"
  proof
    assume "\<exists> C b l r \<sigma>. t1 = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t2 = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> ((b, l, r) \<in> ?CP \<or> (b, r, l) \<in> ?CP)"
    then obtain C b l r \<sigma> where id: "t1 = C\<langle>l \<cdot> \<sigma>\<rangle>" "t2 = C\<langle>r \<cdot> \<sigma>\<rangle>"
      and mem: "(b, l, r) \<in> ?CP \<or> (b, r, l) \<in> ?CP" by blast
    show ?thesis
    proof (cases "l = r")
      case True
      then show ?thesis unfolding id by auto
    next
      case False
      note sub_ctxt = rsteps_closed_ctxt [OF rsteps_closed_subst [OF rsteps_closed_subst]]
      from mem show ?thesis
      proof
        assume mem: "(b, l, r) \<in> ?CP"
        from cp [OF mem False] obtain l' r' s' \<tau> where id2: "l = l' \<cdot> \<tau>" "r = r' \<cdot> \<tau>" and steps: "(l', s') \<in> ?R^*" "(r', s') \<in> ?R^*"
          unfolding instance_rule_def by auto
        show "\<exists> s'. ?p s'" unfolding id id2
          by (rule exI [of _ "C\<langle>s' \<cdot> \<tau> \<cdot> \<sigma>\<rangle>"], rule conjI, rule sub_ctxt [OF steps(1)], rule sub_ctxt [OF steps(2)])
      next
        assume mem: "(b, r, l) \<in> ?CP"
        from cp [OF mem] False obtain l' r' s' \<tau> where id2: "r = l' \<cdot> \<tau>" "l = r' \<cdot> \<tau>" and steps: "(l', s') \<in> ?R^*" "(r', s') \<in> ?R^*"
          unfolding instance_rule_def by auto
        show "\<exists> s'. ?p s'" unfolding id id2
          by (rule exI [of _ "C\<langle>s' \<cdot> \<tau> \<cdot> \<sigma>\<rangle>"], rule conjI, rule sub_ctxt [OF steps(2)], rule sub_ctxt [OF steps(1)])
      qed
    qed
  qed auto
  then show "(t1, t2) \<in> join ?R" by auto
qed

lemma critical_pairs_fork:
  fixes R :: "('f, 'v) trs" and S
  assumes cp: "(b, l, r) \<in> critical_pairs R S"
  shows "(r, l) \<in> (rstep R)\<inverse> O rstep S"
proof -
  from cp obtain m where "(l,m,r) \<in> critical_Peaks R S" 
    unfolding critical_pairs_def critical_Peaks_def by blast
  from critical_Peak_steps(1-2)[OF this] show ?thesis by auto
qed

lemma critical_pairs_fork': assumes "(b,l,r) \<in> critical_pairs R S" 
  shows "(l,r) \<in> (rstep S)^-1 O rstep R" 
  using critical_pairs_fork[OF assms] by auto

(* in the following lemma infiniteness of 'v is crucial, if one restricts to well-formed terms:
   Consider that we only have 5 variables and build the following TRS R = {
     f(g(x1, x2), g(x3, x4)) \<rightarrow> h(x1, h(x2, g(x3, x4)))
     f(g(g(x1, x2), g(x3, x4)), x5) \<rightarrow> h(x5, h(g(x1, x2), g(x3, x4)))
   the following rules are added to allow a join if one the arguments of
   the g's is a not a variable,
     h(g(k(_, _), _), h(_, _)) \<rightarrow> ok for all k \<in> {f, g, h}
     h(g(_, k(_, _)), h(_, _)) \<rightarrow> ok for all k \<in> {f, g, h}
     h(_, h(g(k(_, _), _), _)) \<rightarrow> ok for all k \<in> {f, g, h}
     h(_, h(g(_, k(_, _)), _)) \<rightarrow> ok for all k \<in> {f, g, h}
     h(_, h(_, g(k(_, _), _))) \<rightarrow> ok for all k \<in> {f, g, h}
     h(_, h(_, g(_, k(_, _)))) \<rightarrow> ok for all k \<in> {f, g, h}
     h(g(ok, _), h(_, _)) \<rightarrow> ok
     h(g(_, ok), h(_, _)) \<rightarrow> ok
     h(_, h(g(ok, _), _)) \<rightarrow> ok
     h(_, h(g(_, ok), _)) \<rightarrow> ok
     h(_, h(_, g(ok, _))) \<rightarrow> ok
     h(_, h(_, g(_, ok))) \<rightarrow> ok
   and we allow a join if two of the six arguments are identical
     h(g(x1, x2), h(g(x3, x4), g(x5, x))) \<rightarrow> ok for all x \<in> {x1, .., x5}
     h(g(x1, x2), h(g(x3, x4), g(x, x5))) \<rightarrow> ok for all x \<in> {x1, .., x5}
     h(g(x1, x2), h(g(x3, x), g(x4, x5))) \<rightarrow> ok for all x \<in> {x1, .., x5}
     h(g(x1, x2), h(g(x, x3), g(x4, x5))) \<rightarrow> ok for all x \<in> {x1, .., x5}
     h(g(x1, x), h(g(x2, x3), g(x4, x5))) \<rightarrow> ok for all x \<in> {x1, .., x5}
     h(g(x, x1), h(g(x2, x3), g(x4, x5))) \<rightarrow> ok for all x \<in> {x1, .., x5}
   moreover, we add one rule to join some other critical pairs
     h(x1, ok) \<rightarrow> ok

  note that R is not WCR over the signature {f, g, h, ok} and variables {x1, .., x6} since in the critical pair
  h(g(x1, x2), h(g(x3, x4), g(x5, x6))) \<leftarrow> f(g(g(x1, x2), g(x3, x4)), g(x5, x6)) \<rightarrow> h(g(x5, x6), h(g(x1, x2), g(x3, x4)))
  both h-terms are normal forms.
  However, one can prove that R over the signature {f, g, h, ok} and variables {x1, .., x5} is WCR,
  since the critical pair above cannot be build using only 5 variables, and if one of the arguments is chosen
  as non-variable, or if two arguments are identical, then both terms can be reduced to ok.
  Moreover, all over overlaps can easily be reduced to ok, too.
*)
lemma critical_pairs_complete:
  fixes R :: "('f, 'v) trs"
  assumes cp: "(b, l, r) \<in> critical_pairs R R"
    and no_join: "(l, r) \<notin> (rstep R)\<^sup>\<down>"
  shows "\<not> WCR (rstep R)"
proof
  from critical_pairs_fork [OF cp] obtain u where ul: "(u, l) \<in> rstep R" and ur: "(u, r) \<in> rstep R" by force
  assume wcr: "WCR (rstep R)"
  with ul ur no_join show False unfolding WCR_on_def by auto
qed

lemma critical_pair_lemma:
  fixes R :: "('f, 'v) trs"
  shows "WCR (rstep R) \<longleftrightarrow>
    (\<forall> (b, s, t) \<in> critical_pairs R R. (s, t) \<in> (rstep R)\<^sup>\<down>)"
    (is "?l = ?r")
proof
  assume ?l
  with critical_pairs_complete [where R = R] show ?r by auto
next
  assume ?r
  show ?l
  proof (rule critical_pairs)
    fix b s t
    assume "(b, s, t) \<in> critical_pairs R R"
    with \<open>?r\<close> have "(s, t) \<in> join (rstep R)" by auto
    then obtain u where s: "(s, u) \<in> (rstep R)^*"
      and t: "(t, u) \<in> (rstep R)^*" by auto
    show "\<exists> s' t' u. instance_rule (s, t) (s', t') \<and> (s', u) \<in> (rstep R)^* \<and> (t', u) \<in> (rstep R)^*"
    proof (intro exI conjI)
      show "instance_rule (s, t) (s, t)" by simp
    qed (insert s t, auto)
  qed
qed

lemma critical_pairs_exI:
  fixes \<sigma> :: "('f, 'v) subst"
  assumes P: "(l, r) \<in> P" and R: "(l', r') \<in> R" and l: "l = C\<langle>l''\<rangle>"
    and l'': "is_Fun l''" and unif: "l'' \<cdot> \<sigma> = l' \<cdot> \<tau>"
    and b: "b = (C = \<box>)"
  shows "\<exists> s t. (b, s, t) \<in> critical_pairs P R"
proof -
  from mgu_vd_complete [OF unif]
  obtain \<mu>1 \<mu>2  where mgu: "mgu_vd ren l'' l' = Some (\<mu>1, \<mu>2)" by blast
  show ?thesis
    by (intro exI, rule critical_pairsI [OF P R l l'' mgu refl refl b])
qed

end
end