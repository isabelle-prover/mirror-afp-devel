header "Splay Tree Analysis"

theory Splay_Tree_Analysis
imports
  Splay_Tree_Analysis_Base
  Amor
begin

subsection "Analysis of splay"

definition A :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> real" where
"A a t = t_splay a t + \<Phi>(splay a t) - \<Phi> t"

lemma A_simps[simp]: "A a (Node l a r) = 0"
 "a<b \<Longrightarrow> A a (Node (Node ll a lr) b r) = \<phi> (Node lr b r) - \<phi> (Node ll a lr)"
 "b<a \<Longrightarrow> A a (Node l b (Node rl a rr)) = \<phi> (Node rl b l) - \<phi> (Node rl a rr)"
by(auto simp add: A_def algebra_simps real_of_nat_Suc)

lemma A_ub: "\<lbrakk> bst t; Node la a ra : subtrees t \<rbrakk>
  \<Longrightarrow> A a t \<le> 3 * (\<phi> t - \<phi>(Node la a ra))"
proof(induction a t rule: splay.induct)
  case 1 thus ?case by simp
next
  case (2 a l c r)
  let ?A = "Node la a ra" let ?C = "Node l c r"
  have a: "a : insert c (set_tree l Un set_tree r)" using "2.prems"(2)
    by (metis Node_notin_subtrees_if tree.set(2))
  show ?case
  proof cases
    assume "a=c"
    thus ?thesis using "2.prems" by (auto simp: real_of_nat_Suc)
  next
    assume "a\<noteq>c"
    hence "a<c \<or> c<a" by (metis neqE)
    thus ?thesis
    proof
      assume "a<c"
      then obtain ll b lr where [simp]: "l = Node ll b lr"
        using "2.prems"(1,2)
        by (cases l) (auto, metis in_set_tree_if less_asym)
      let ?B = "Node ll b lr"  let ?C' = "Node lr c r"
      have "b < c" using "2.prems"(1,2) by (auto)
      hence "b \<notin> set_tree r" using "2.prems"(1) by auto
      show ?thesis
      proof cases
        assume "a=b"
        thus ?thesis using "2.prems"(1,2) `a<c` `b \<notin> set_tree r`
          log_le_cancel_iff[of 2 "size1 ?C'" "size1 ?C"]
          log_le_cancel_iff[of 2 "size1 ?B" "size1 ?C"]
          by (auto simp: real_of_nat_Suc field_simps simp del:log_le_cancel_iff)
      next
        assume "a\<noteq>b"
        hence "a<b \<or> b<a" by (metis neqE)
        thus ?thesis
        proof
          assume "a<b"
          hence 0: "a \<notin> set_tree lr \<and> a \<notin> set_tree r"
            using "2.prems"(1) by auto
          hence 1: "a \<in> set_tree ll" using "2.prems" `a<b` by (auto)
          then obtain l' u r' where sp: "splay a ll = Node l' u r'"
            using "2.prems"(1,2) by(cases "splay a ll") auto
          have "ll \<noteq> Leaf" using 1 by auto
          let ?R = ll  let ?R' = "Node l' u r'"  let ?B' = "Node r' b ?C'"
          have "A a ?C = A a ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B - \<phi> ?R' + 1"
            using "2.prems" 1 sp
              by(auto simp: A_def size_if_splay algebra_simps real_of_nat_Suc split: tree.split)
          also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B - \<phi> ?R' + 1 - 3 * \<phi> ?A"
            using "2.IH"(1)[OF `a\<noteq>c` `a<c` `l = Node ll b lr` `a\<noteq>b`] `ll \<noteq> Leaf` `a<b` "2.prems" 0
            by(auto simp: algebra_simps)
          also have "\<dots> = 2 * \<phi> ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B + 1 - 3 * \<phi> ?A"
            using sp by(simp add: size_if_splay)
          also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?C' + 1 - 3 * \<phi> ?A" by(simp)
          also have "\<dots> \<le> \<phi> ?B' + 2 * \<phi> ?C - 3 * \<phi> ?A"
            using sp add_log_log1[of "size1 ?R" "size1 ?C'"]
            by(simp add: size_if_splay real_of_nat_Suc)
          also have "\<dots> \<le> 3 * \<phi> ?C - 3 * \<phi> ?A"
            using sp by(simp add: size_if_splay)
          finally show ?thesis by simp
       next
          assume "b<a"
          hence 0: "a \<notin> set_tree ll \<and> a \<notin> set_tree r"
            using "2.prems"(1) `a < c` by(auto)
          hence 1: "a \<in> set_tree lr" using "2.prems" `b<a` `a<c` by (auto)
          then obtain l' u r' where sp: "splay a lr = Node l' u r'"
            using "2.prems"(1,2) by(cases "splay a lr") auto
          have "lr \<noteq> Leaf" using 1 by auto
          let ?R = lr  let ?R' = "Node l' u r'"
          let ?B' = "Node ll b l'"  let ?C' = "Node r' c r"
          have "A a ?C = A a ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B - \<phi> ?R' + 1"
            using "2.prems" 1 sp
              by(auto simp: A_def size_if_splay algebra_simps real_of_nat_Suc split: tree.split)
          also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B - \<phi> ?R' + 1 - 3 * \<phi> ?A"
            using "2.IH"(2)[OF `a\<noteq>c` `a<c` `l = Node ll b lr` `a\<noteq>b`] `lr \<noteq> Leaf` `a\<noteq>c` `b<a` "2.prems" 0
            by(auto simp: algebra_simps)
          also have "\<dots> = 2 * \<phi> lr + \<phi> ?B' + \<phi> ?C' - \<phi> ?B + 1 - 3 * \<phi> ?A"
            using sp by(simp add: size_if_splay)
          also have "\<dots> \<le> \<phi> lr + \<phi> ?B' + \<phi> ?C' + 1 - 3 * \<phi> ?A" by(simp)
          also have "\<dots> \<le> \<phi> lr + 2 * \<phi> ?C - 3 * \<phi> ?A"
            using sp add_log_log1[of "size1 ?B'" "size1 ?C'"]
            by(simp add: size_if_splay real_of_nat_Suc)
          also have "\<dots> \<le> 3 * \<phi> ?C - 3 * \<phi> ?A" by(simp)
          finally show ?thesis by simp
        qed
      qed
    next
      assume "c<a"
      then obtain rl b rr where [simp]: "r = Node rl b rr"
        using "2.prems"(1,2)
        by (cases r) (auto, metis in_set_tree_if less_asym)
      let ?B = "Node rl b rr"  let ?C' = "Node l c rl"
      have "c < b" using "2.prems"(1,2) by (auto)
      hence "b \<notin> set_tree l" using "2.prems"(1) by auto
      show ?thesis
      proof cases
        assume "a=b"
        thus ?thesis using "2.prems"(1,2) `c<a` `b \<notin> set_tree l`
          log_le_cancel_iff[of 2 "size1 ?C'" "size1 ?C"]
          log_le_cancel_iff[of 2 "size1 ?B" "size1 ?C"]
          by (auto simp: real_of_nat_Suc field_simps simp del:log_le_cancel_iff)
      next
        assume "a\<noteq>b"
        hence "a<b \<or> b<a" by (metis neqE)
        thus ?thesis
        proof
          assume "a<b"
          hence 0: "a \<notin> set_tree rr \<and> a \<notin> set_tree l"
            using "2.prems"(1) `c<a` by (auto)
          hence 1: "a \<in> set_tree rl" using "2.prems" `c<a` `a<b` by (auto)
          then obtain l' u r' where sp: "splay a rl = Node l' u r'"
            using "2.prems"(1,2) by(cases "splay a rl") auto
          have "rl \<noteq> Leaf" using 1 by auto
          let ?R = rl  let ?R' = "Node l' u r'"
          let ?B' = "Node r' b rr"  let ?C' = "Node l c l'"
          have "A a ?C = A a ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B - \<phi> ?R' + 1"
            using "2.prems" 1 sp
              by(auto simp: A_def size_if_splay algebra_simps real_of_nat_Suc split: tree.split)
          also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B - \<phi> ?R' + 1 - 3 * \<phi> ?A"
            using "2.IH"(3)[OF `a\<noteq>c` order_less_not_sym[OF `c<a`] `r = Node rl b rr` `a\<noteq>b`]
              `rl \<noteq> Leaf` `a\<noteq>c` `a<b` "2.prems" 0 by(auto simp: algebra_simps)
          also have "\<dots> = 2 * \<phi> ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B + 1 - 3 * \<phi> ?A"
            using sp by(simp add: size_if_splay)
          also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?C' + 1 - 3 * \<phi> ?A" by(simp)
          also have "\<dots> \<le> \<phi> ?R + 2 * \<phi> ?C - 3 * \<phi> ?A"
            using sp add_log_log1[of "size1 ?B'" "size1 ?C'"]
            by(simp add: size_if_splay real_of_nat_Suc algebra_simps)
          also have "\<dots> \<le> 3 * \<phi> ?C - 3 * \<phi> ?A" by(simp)
          finally show ?thesis by simp
        next
          assume "b<a"
          hence 0: "a \<notin> set_tree rl \<and> a \<notin> set_tree l"
            using "2.prems"(1) `b<a` by(auto)
          hence 1: "a \<in> set_tree rr" using "2.prems" `b<a` `c<a` by (auto)
          then obtain l' u r' where sp: "splay a rr = Node l' u r'"
            using "2.prems"(1,2) by(cases "splay a rr") auto
          have "rr \<noteq> Leaf" using 1 by auto
          let ?R = rr  let ?R' = "Node l' u r'"  let ?B' = "Node ?C' b l'"
          have "A a ?C = A a ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B - \<phi> ?R' + 1"
            using "2.prems" 1 sp
              by(auto simp: A_def size_if_splay algebra_simps real_of_nat_Suc split: tree.split)
          also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?C' - \<phi> ?B - \<phi> ?R' + 1 - 3 * \<phi> ?A"
            using "2.IH"(4)[OF `a\<noteq>c` order_less_not_sym[OF `c<a`] `r = Node rl b rr` `a\<noteq>b`]
              `rr \<noteq> Leaf` `b<a` "2.prems" 0 by(auto simp: algebra_simps)
          also have "\<dots> = 2 * \<phi> rr + \<phi> ?B' + \<phi> ?C' - \<phi> ?B + 1 - 3 * \<phi> ?A"
            using sp by(simp add: size_if_splay)
          also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?C' + 1 - 3 * \<phi> ?A" by(simp)
          also have "\<dots> \<le> \<phi> ?B' + 2 * \<phi> ?C - 3 * \<phi> ?A"
            using sp add_log_log1[of "size1 ?R" "size1 ?C'"]
            by(simp add: size_if_splay real_of_nat_Suc algebra_simps)
          also have "\<dots> \<le> 3 * \<phi> ?C - 3 * \<phi> ?A"
            using sp by(simp add: size_if_splay)
          finally show ?thesis by simp
        qed
      qed
    qed
  qed
qed

lemma A_ub2: assumes "bst t" "a : set_tree t"
shows "A a t \<le> 3 * (\<phi> t - 1)"
proof -
  from assms(2) obtain la ra where N: "Node la a ra : subtrees t"
    by (metis set_treeE)
  have "A a t \<le> 3 * (\<phi> t - \<phi>(Node la a ra))" by(rule A_ub[OF assms(1) N])
  also have "\<dots> \<le> 3 * (\<phi> t - 1)" by(simp add: field_simps)
  finally show ?thesis .
qed

lemma A_ub3: assumes "bst t" shows "A a t \<le> 3 * \<phi> t"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: A_def)
next
  assume "t \<noteq> Leaf"
  from ex_in_set_tree[OF this assms] obtain a' where
    a': "a' \<in> set_tree t"  "splay a' t = splay a t"  "t_splay a' t = t_splay a t"
    by blast
  have [arith]: "log 2 2 > 0" by simp
  show ?thesis using A_ub2[OF assms a'(1)] by(simp add: A_def a' log_divide)
qed


definition Am :: "'a::linorder tree \<Rightarrow> real" where
"Am t = t_splay_max t + \<Phi>(splay_max t) - \<Phi> t"

lemma Am_ub: "\<lbrakk> bst t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow> Am t \<le> 3 * (\<phi> t - 1)"
proof(induction t rule: splay_max.induct)
  case 1 thus ?case by (simp)
next
  case (2 l b)
  thus ?case using one_le_log_cancel_iff[of 2 "size1 l + 1"]
    by (simp add: Am_def del: one_le_log_cancel_iff)
next
  case (3 l b rl c rr)
  show ?case
  proof cases
    assume "rr = Leaf"
    thus ?thesis
      using one_le_log_cancel_iff[of 2 "1 + size1 rl"]
        one_le_log_cancel_iff[of 2 "1 + size1 l + size1 rl"]
        log_le_cancel_iff[of 2 "size1 l + size1 rl" "1 + size1 l + size1 rl"]
     by (auto simp: real_of_nat_Suc Am_def field_simps
           simp del: log_le_cancel_iff one_le_log_cancel_iff)
  next
    assume "rr \<noteq> Leaf"
    then obtain l' u r' where sp: "splay_max rr = Node l' u r'"
      using splay_max_Leaf_iff tree.exhaust by blast
    hence 1: "size rr = size l' + size r' + 1"
      using size_splay_max[of rr,symmetric] by(simp)
    let ?C = "Node rl c rr"  let ?B = "Node l b ?C"
    let ?B' = "Node l b rl"  let ?C' = "Node ?B' c l'"
    have "Am ?B = Am rr + \<phi> ?B' + \<phi> ?C' - \<phi> rr - \<phi> ?C + 1" using "3.prems" sp 1
      by(auto simp add: Am_def real_of_nat_Suc)
    also have "\<dots> \<le> 3 * (\<phi> rr - 1) + \<phi> ?B' + \<phi> ?C' - \<phi> rr - \<phi> ?C + 1"
      using 3 `rr \<noteq> Leaf` by auto
    also have "\<dots> = 2 * \<phi> rr + \<phi> ?B' + \<phi> ?C' - \<phi> ?C - 2" by simp
    also have "\<dots> \<le> \<phi> rr + \<phi> ?B' + \<phi> ?C' - 2" by simp
    also have "\<dots> \<le> 2 * \<phi> ?B + \<phi> ?C' - 3"
      using add_log_log1[of "size1 ?B'" "size1 rr"] by(simp add: real_of_nat_Suc)
    also have "\<dots> \<le> 3 * \<phi> ?B - 3" using 1 by simp
    finally show ?case by simp
  qed
qed

lemma Am_ub3: assumes "bst t" shows "Am t \<le> 3 * \<phi> t"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: Am_def)
next
  assume "t \<noteq> Leaf"
  have [arith]: "log 2 2 > 0" by simp
  show ?thesis using Am_ub[OF assms `t \<noteq> Leaf`] by(simp add: Am_def)
qed


subsection "Overall analysis"

interpretation ST: amor
where init = Leaf and nxt = nxt\<^sub>s\<^sub>t and inv = bst
and t = t\<^sub>s\<^sub>t and \<Phi> = \<Phi>
and U = "\<lambda>f t. case f of
  Splay _ \<Rightarrow> 3 * log 2 (size1 t) |
  Insert _ \<Rightarrow> 4 * log 2 (size1 t) + 1 |
  Delete _ \<Rightarrow> 6 * log 2 (size1 t)"
proof
  case goal1 show ?case by simp
next
  case goal2 show ?case
  proof (cases f)
    case (Splay a)
    with bst_splay[OF goal2, of a] show ?thesis by (auto split: tree.split)
  next
    case (Insert a)
    with bst_splay[OF goal2, of a] show ?thesis
      by (auto simp: splay_bstL[OF goal2] splay_bstR[OF goal2] split: tree.split)
  next
    case (Delete a)[simp]
    with goal2 show ?thesis by(simp add: bst_delete)
  qed
next
  case goal3 show ?case
    by(induction s)(simp_all)
next
  case goal4 show ?case by simp
next
  case goal5
  show ?case (is "?l \<le> ?r")
  proof(cases f)
    case (Splay a)
    thus ?thesis using A_ub3[OF goal5] by(simp add: A_def)
  next
    case (Insert a)[simp]
    show ?thesis
    proof cases
      assume "s = Leaf" thus ?thesis by(simp)
    next
      assume "s \<noteq> Leaf"
      then obtain l e r where [simp]: "splay a s = Node l e r"
        by (metis tree.exhaust splay_Leaf_iff)
      let ?t = "real(t_splay a s)"
      let ?Plr = "\<Phi> l + \<Phi> r"  let ?Ps = "\<Phi> s"
      let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
      have opt: "?t + \<Phi> (splay a s) - ?Ps  \<le> 3 * log 2 (real (size1 s))"
        using A_ub3[OF goal5, simplified A_def, of a] by (simp)
      from less_linear[of e a]
      show ?thesis
      proof (elim disjE)
        assume "e=a"
        have nneg: "log 2 (1 + real (size s)) \<ge> 0" by simp
        thus ?thesis using `s \<noteq> Leaf` opt `e=a`
          apply(simp add: algebra_simps real_of_nat_Suc) using nneg by arith
      next
        let ?L = "log 2 (real(size1 l) + 1)"
        assume "e<a" hence "e \<noteq> a" by simp
        hence "?l = (?t + ?Plr - ?Ps) + ?L + ?LR"
          using  `s \<noteq> Leaf` `e<a` by(simp add: real_of_nat_Suc)
        also have "?t + ?Plr - ?Ps \<le> 2 * log 2 ?slr"
          using opt size_splay[of a s,symmetric] by(simp add: real_of_nat_Suc)
        also have "?L \<le> log 2 ?slr" by(simp)
        also have "?LR \<le> log 2 ?slr + 1"
        proof -
          have "?LR \<le> log 2 (2 * ?slr)" by (simp add: real_of_nat_Suc)
          also have "\<dots> \<le> log 2 ?slr + 1"
            by (simp add: log_mult del:distrib_left_numeral)
          finally show ?thesis .
        qed
        finally show ?thesis using size_splay[of a s,symmetric]
          by (simp add: real_of_nat_Suc)
      next
        let ?R = "log 2 (2 + real(size r))"
        assume "a<e" hence "e \<noteq> a" by simp
        hence "?l = (?t + ?Plr - ?Ps) + ?R + ?LR"
          using  `s \<noteq> Leaf` `a<e` by(simp add: real_of_nat_Suc)
        also have "?t + ?Plr - ?Ps \<le> 2 * log 2 ?slr"
          using opt size_splay[of a s,symmetric]
          by(simp add: real_of_nat_Suc)
        also have "?R \<le> log 2 ?slr" by(simp)
        also have "?LR \<le> log 2 ?slr + 1"
        proof -
          have "?LR \<le> log 2 (2 * ?slr)" by (simp add: real_of_nat_Suc)
          also have "\<dots> \<le> log 2 ?slr + 1"
            by (simp add: log_mult del:distrib_left_numeral)
          finally show ?thesis .
        qed
        finally show ?thesis using size_splay[of a s,symmetric]
           by (simp add: real_of_nat_Suc)
      qed
    qed
  next
    case (Delete a)[simp]
    show ?thesis
    proof (cases s)
      case Leaf thus ?thesis by(simp add: delete_def t_delete_def)
    next
      case (Node ls x rs)[simp]
      then obtain l e r where sp[simp]: "splay a (Node ls x rs) = Node l e r"
        by (metis tree.exhaust splay_Leaf_iff)
      let ?t = "real(t_splay a s)"
      let ?Plr = "\<Phi> l + \<Phi> r"  let ?Ps = "\<Phi> s"
      let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
      let ?lslr = "log 2 (2 + (real (size ls) + real (size rs)))"
      have "?lslr \<ge> 0" by simp
      have opt: "?t + \<Phi> (splay a s) - ?Ps  \<le> 3 * log 2 (real (size1 s))"
        using A_ub3[OF goal5, simplified A_def, of a]
        by (simp add: field_simps)
      show ?thesis
      proof (cases "e=a")
        case False thus ?thesis
          using opt apply(simp add: delete_def t_delete_def field_simps real_of_nat_Suc)
          using `?lslr \<ge> 0` by arith
      next
        case True[simp]
        show ?thesis
        proof (cases l)
          case Leaf
          have 1: "log 2 (2 + real (size r)) \<ge> 0" by(simp)
          show ?thesis
            using Leaf opt apply(simp add: delete_def t_delete_def field_simps real_of_nat_Suc)
            using 1 `?lslr \<ge> 0` by arith
        next
          case (Node ll y lr)
          then obtain l' y' r' where [simp]:
            "splay_max (Node ll y lr) = Node l' y' r'"
            using splay_max_Leaf_iff tree.exhaust by blast
          have "bst l" using bst_splay[OF goal5, of a] by simp
          have "\<Phi> r' \<ge> 0" apply (induction r') by (auto)
          have optm: "real(t_splay_max l) + \<Phi> (splay_max l) - \<Phi> l  \<le> 3 * \<phi> l"
            using Am_ub3[OF `bst l`, simplified Am_def]
            by (simp add: field_simps Node)
          have 1: "log 2 (2+(real(size l')+real(size r))) \<le> log 2 (2+(real(size l)+real(size r)))"
            using size_splay_max[of l] Node by simp
          have 2: "log 2 (2 + (real (size l') + real (size r'))) \<ge> 0" by simp
          have 3: "log 2 (size1 l' + size1 r) \<le> log 2 (size1 l' + size1 r') + log 2 ?slr"
            apply(simp add: real_of_nat_Suc) using 1 2 by arith
          have 4: "log 2 (2 + (real(size ll) + real(size lr))) \<le> ?lslr"
            using size_if_splay[OF sp] Node by simp
          show ?thesis using add_mono[OF opt optm] Node 3
            apply(simp add: delete_def t_delete_def field_simps real_of_nat_Suc)
            using 4 `\<Phi> r' \<ge> 0` by arith
        qed
      qed
    qed
  qed
qed

end
