section "Splay Tree Analysis"

theory Splay_Tree_Analysis
imports
  Splay_Tree_Analysis_Base
  Amor
begin

subsection "Analysis of splay"

definition A :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> real" where
"A a t = t_splay a t + \<Phi>(splay a t) - \<Phi> t"

lemma A_simps[simp]: "A a (Node l a r) = 1"
 "a<b \<Longrightarrow> A a (Node (Node ll a lr) b r) = \<phi> (Node lr b r) - \<phi> (Node ll a lr) + 1"
 "b<a \<Longrightarrow> A a (Node l b (Node rl a rr)) = \<phi> (Node rl b l) - \<phi> (Node rl a rr) + 1"
by(auto simp add: A_def algebra_simps)

text{* The following lemma is an attempt to prove a generic lemma that covers
both zig-zig cases. However, the lemma is not as nice as one would like.
Hence it is used only once, as a demo. Ideally the lemma would involve
function @{const A}, but that is impossible because this involves @{const splay}
and thus depends on the ordering. We would need a truly symmetric version of @{const splay}
that takes the ordering as an explicit argument. Then we could define
all the symmetric cases by one final equation
@{term"splay2 less t = splay2 (not o less) (mirror t)"}.
This would simplify the code and the proofs. *}

lemma zig_zig: fixes lx x rx lb b rb a ra u lb1 lb2
defines [simp]: "X == Node lx (x) rx" defines[simp]: "B == Node lb b rb"
defines [simp]: "t == Node B a ra" defines [simp]: "A' == Node rb a ra"
defines [simp]: "t' == Node lb1 u (Node lb2 b A')"
assumes hyps: "lb \<noteq> \<langle>\<rangle>" and IH: "t_splay x lb + \<Phi> lb1 + \<Phi> lb2 - \<Phi> lb \<le> 2 * \<phi> lb - 3 * \<phi> X + 1" and
 prems: "size lb = size lb1 + size lb2 + 1" "X \<in> subtrees lb"
shows "t_splay x lb + \<Phi> t' - \<Phi> t \<le> 3 * (\<phi> t - \<phi> X)"
proof -
  def [simp]: B' == "Node lb2 b A'"
  have "t_splay x lb + \<Phi> t' - \<Phi> t = t_splay x lb + \<Phi> lb1 + \<Phi> lb2 - \<Phi> lb + \<phi> B' + \<phi> A' - \<phi> B"
    using prems
    by(auto simp: A_def size_if_splay algebra_simps in_set_tree_if split: tree.split)
  also have "\<dots> \<le> 2 * \<phi> lb + \<phi> B' + \<phi> A' - \<phi> B - 3 * \<phi> X + 1"
    using IH prems(2) by(auto simp: algebra_simps)
  also have "\<dots> \<le> \<phi> lb + \<phi> B' + \<phi> A' - 3 * \<phi> X + 1" by(simp)
  also have "\<dots> \<le> \<phi> B' + 2 * \<phi> t - 3 * \<phi> X "
    using prems ld_ld_1_less[of "size1 lb" "size1 A'"]
    by(simp add: size_if_splay)
  also have "\<dots> \<le> 3 * \<phi> t - 3 * \<phi> X"
    using prems by(simp add: size_if_splay)
  finally show ?thesis by simp
qed

lemma A_ub: "\<lbrakk> bst t; Node lx x rx : subtrees t \<rbrakk>
  \<Longrightarrow> A x t \<le> 3 * (\<phi> t - \<phi>(Node lx x rx)) + 1"
proof(induction x t rule: splay.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by auto
next
  case 4 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 5 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 7 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 10 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 12 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 13 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case (3 b a lb rb ra)
  let ?A = "Node (Node lb b rb) a ra"
  have "b \<notin> set_tree ra" using "3.prems"(1) by auto
  with 3 show ?case using
    log_le_cancel_iff[of 2 "size1(Node rb a ra)" "size1 ?A"]
    log_le_cancel_iff[of 2 "size1(Node lb b rb)" "size1 ?A"]
    by (auto simp: algebra_simps simp del:log_le_cancel_iff)
next
  case (9 a b la lb rb)
  let ?A = "\<langle>la, a, \<langle>lb, b, rb\<rangle>\<rangle>"
  have "b \<notin> set_tree la" using "9.prems"(1) by auto
  with 9 show ?case using
    log_le_cancel_iff[of 2 "size1(Node la a lb)" "size1 ?A"]
    log_le_cancel_iff[of 2 "size1(Node lb b rb)" "size1 ?A"]
    by (auto simp: algebra_simps simp del:log_le_cancel_iff)
next
  case (6 x b a lb rb ra)
  hence 0: "x \<notin> set_tree rb \<and> x \<notin> set_tree ra" using "6.prems"(1) by auto
  hence 1: "x \<in> set_tree lb" using "6.prems" `x<b` by (auto)
  obtain lu u ru where sp: "splay x lb = Node lu u ru"
    using splay_not_Leaf[OF \<open>lb \<noteq> Leaf\<close>] by blast
  let ?X = "Node lx x rx" let ?B = "Node lb b rb"  let ?A = "Node ?B a ra"
  let ?R = lb  let ?R' = "Node lu u ru"
  let ?A' = "Node rb a ra"  let ?B' = "Node ru b ?A'"
  have "A x ?A = A x ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' + 1"
    using "6.prems" 1 sp
    by(auto simp: A_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' - 3 * \<phi> ?X + 2"
    using 6 0 by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?A' - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> ?B' + 2 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?R" "size1 ?A'"]
    by(simp add: size_if_splay)
  also have "\<dots> \<le> 3 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp by(simp add: size_if_splay)
  finally show ?case by simp
next
  case (8 x a b rb lb ra)
  hence 0: "x \<notin> set_tree lb \<and> x \<notin> set_tree ra"
    using "8.prems"(1) `x < a` by(auto)
  hence 1: "x \<in> set_tree rb" using "8.prems" `b<x` `x<a` by (auto)
  obtain lu u ru where sp: "splay x rb = Node lu u ru"
     using splay_not_Leaf[OF \<open>rb \<noteq> Leaf\<close>] by blast
  let ?X = "Node lx x rx" let ?B = "Node lb b rb"  let ?A = "Node ?B a ra"
  let ?R = rb  let ?R' = "Node lu u ru"
  let ?B' = "Node lb b lu"  let ?A' = "Node ru a ra"
  have "A x ?A = A x ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' + 1"
    using "8.prems" 1 sp
    by(auto simp: A_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' - 3 * \<phi> ?X + 2"
    using 8 0 by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> rb + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> rb + \<phi> ?B' + \<phi> ?A' - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> rb + 2 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?B'" "size1 ?A'"]
    by(simp add: size_if_splay)
  also have "\<dots> \<le> 3 * \<phi> ?A - 3 * \<phi> ?X + 1" by(simp)
  finally show ?case by simp
next
  case (11 a x b lb la rb)
  hence 0: "x \<notin> set_tree rb \<and> x \<notin> set_tree la"
    using "11.prems"(1) `a<x` by (auto)
  hence 1: "x \<in> set_tree lb" using "11.prems" `a<x` `x<b` by (auto)
  obtain lu u ru where sp: "splay x lb = Node lu u ru"
    using splay_not_Leaf[OF \<open>lb \<noteq> Leaf\<close>] by blast
  let ?X = "Node lx x rx" let ?B = "Node lb b rb"  let ?A = "Node la a ?B"
  let ?R = lb  let ?R' = "Node lu u ru"
  let ?B' = "Node ru b rb"  let ?A' = "Node la a lu"
  have "A x ?A = A x ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' + 1"
    using "11.prems" 1 sp
    by(auto simp: A_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' - 3 * \<phi> ?X + 2"
    using 11 0 by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?A' - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> ?R + 2 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?B'" "size1 ?A'"]
    by(simp add: size_if_splay algebra_simps)
  also have "\<dots> \<le> 3 * \<phi> ?A - 3 * \<phi> ?X + 1" by(simp)
  finally show ?case by simp
next
  case (14 a x b rb la lb)
  hence 0: "x \<notin> set_tree lb \<and> x \<notin> set_tree la"
    using "14.prems"(1) `b<x` by(auto)
  hence 1: "x \<in> set_tree rb" using "14.prems" `b<x` `a<x` by (auto)
  obtain lu u ru where sp: "splay x rb = Node lu u ru"
    using splay_not_Leaf[OF \<open>rb \<noteq> Leaf\<close>] by blast
  from zig_zig[of rb x ru lu lx rx _ b lb a la] 14 sp 0
  show ?case by(auto simp: A_def size_if_splay algebra_simps)
(* The explicit version:
  have "A x ?A = A x ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' + 1"
    using "14.prems" 1 sp
    by(auto simp: A_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' - 3 * \<phi> ?X + 2"
    using 14 0 by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> rb + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?A' - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> ?B' + 2 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?R" "size1 ?A'"]
    by(simp add: size_if_splay algebra_simps)
  also have "\<dots> \<le> 3 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp by(simp add: size_if_splay)
  finally show ?case by simp
*)
qed

lemma A_ub2: assumes "bst t" "a : set_tree t"
shows "A a t \<le> 3 * (\<phi> t - 1) + 1"
proof -
  from assms(2) obtain la ra where N: "Node la a ra : subtrees t"
    by (metis set_treeE)
  have "A a t \<le> 3 * (\<phi> t - \<phi>(Node la a ra)) + 1" by(rule A_ub[OF assms(1) N])
  also have "\<dots> \<le> 3 * (\<phi> t - 1) + 1" by(simp add: field_simps)
  finally show ?thesis .
qed

lemma A_ub3: assumes "bst t" shows "A a t \<le> 3 * \<phi> t + 1"
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

lemma Am_ub: "\<lbrakk> bst t; t \<noteq> Leaf \<rbrakk> \<Longrightarrow> Am t \<le> 3 * (\<phi> t - 1) + 1"
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
     by (auto simp: Am_def field_simps
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
      by(auto simp add: Am_def)
    also have "\<dots> \<le> 3 * (\<phi> rr - 1) + \<phi> ?B' + \<phi> ?C' - \<phi> rr - \<phi> ?C + 2"
      using 3 `rr \<noteq> Leaf` by auto
    also have "\<dots> = 2 * \<phi> rr + \<phi> ?B' + \<phi> ?C' - \<phi> ?C - 1" by simp
    also have "\<dots> \<le> \<phi> rr + \<phi> ?B' + \<phi> ?C' - 1" by simp
    also have "\<dots> \<le> 2 * \<phi> ?B + \<phi> ?C' - 2"
      using ld_ld_1_less[of "size1 ?B'" "size1 rr"] by(simp add:)
    also have "\<dots> \<le> 3 * \<phi> ?B - 2" using 1 by simp
    finally show ?case by simp
  qed
qed

lemma Am_ub3: assumes "bst t" shows "Am t \<le> 3 * \<phi> t + 1"
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
  Splay _ \<Rightarrow> 3 * log 2 (size1 t) + 1 |
  Insert _ \<Rightarrow> 4 * log 2 (size1 t) + 2 |
  Delete _ \<Rightarrow> 6 * log 2 (size1 t) + 2"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case (2 a f) show ?case
  proof (cases f)
    case (Splay a)
    with bst_splay[OF 2, of a] show ?thesis by (auto split: tree.split)
  next
    case (Insert a)
    with bst_splay[OF 2, of a] show ?thesis
      by (auto simp: splay_bstL[OF 2] splay_bstR[OF 2] split: tree.split)
  next
    case [simp]: (Delete a)
    with 2 show ?thesis by(simp add: bst_delete)
  qed
next
  case (3 s) show ?case
    by(induction s)(simp_all)
next
  case 4 show ?case by simp
next
  case (5 s f)
  show ?case (is "?l \<le> ?r")
  proof(cases f)
    case (Splay a)
    thus ?thesis using A_ub3[OF 5] by(simp add: A_def)
  next
    case [simp]: (Insert a)
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
      have opt: "?t + \<Phi> (splay a s) - ?Ps  \<le> 3 * log 2 (real (size1 s)) + 1"
        using A_ub3[OF 5, simplified A_def, of a] by (simp)
      from less_linear[of e a]
      show ?thesis
      proof (elim disjE)
        assume "e=a"
        have nneg: "log 2 (1 + real (size s)) \<ge> 0" by simp
        thus ?thesis using `s \<noteq> Leaf` opt `e=a`
          apply(simp add: algebra_simps) using nneg by arith
      next
        let ?L = "log 2 (real(size1 l) + 1)"
        assume "e<a" hence "e \<noteq> a" by simp
        hence "?l = (?t + ?Plr - ?Ps) + ?L + ?LR"
          using  `s \<noteq> Leaf` `e<a` by(simp add:)
        also have "?t + ?Plr - ?Ps \<le> 2 * log 2 ?slr + 1"
          using opt size_splay[of a s,symmetric] by(simp add:)
        also have "?L \<le> log 2 ?slr" by(simp)
        also have "?LR \<le> log 2 ?slr + 1"
        proof -
          have "?LR \<le> log 2 (2 * ?slr)" by (simp add:)
          also have "\<dots> \<le> log 2 ?slr + 1"
            by (simp add: log_mult del:distrib_left_numeral)
          finally show ?thesis .
        qed
        finally show ?thesis using size_splay[of a s,symmetric]
          by (simp add:)
      next
        let ?R = "log 2 (2 + real(size r))"
        assume "a<e" hence "e \<noteq> a" by simp
        hence "?l = (?t + ?Plr - ?Ps) + ?R + ?LR"
          using  `s \<noteq> Leaf` `a<e` by(simp add:)
        also have "?t + ?Plr - ?Ps \<le> 2 * log 2 ?slr + 1"
          using opt size_splay[of a s,symmetric]
          by(simp add:)
        also have "?R \<le> log 2 ?slr" by(simp)
        also have "?LR \<le> log 2 ?slr + 1"
        proof -
          have "?LR \<le> log 2 (2 * ?slr)" by (simp add:)
          also have "\<dots> \<le> log 2 ?slr + 1"
            by (simp add: log_mult del:distrib_left_numeral)
          finally show ?thesis .
        qed
        finally show ?thesis using size_splay[of a s,symmetric]
           by (simp add:)
      qed
    qed
  next
    case [simp]: (Delete a)
    show ?thesis
    proof (cases s)
      case Leaf thus ?thesis by(simp add: Splay_Tree.delete_def t_delete_def)
    next
      case [simp]: (Node ls x rs)
      then obtain l e r where sp[simp]: "splay a (Node ls x rs) = Node l e r"
        by (metis tree.exhaust splay_Leaf_iff)
      let ?t = "real(t_splay a s)"
      let ?Plr = "\<Phi> l + \<Phi> r"  let ?Ps = "\<Phi> s"
      let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
      let ?lslr = "log 2 (real (size ls) + (real (size rs) + 2))"
      have "?lslr \<ge> 0" by simp
      have opt: "?t + \<Phi> (splay a s) - ?Ps  \<le> 3 * log 2 (real (size1 s)) + 1"
        using A_ub3[OF 5, simplified A_def, of a]
        by (simp add: field_simps)
      show ?thesis
      proof (cases "e=a")
        case False thus ?thesis
          using opt apply(simp add: Splay_Tree.delete_def t_delete_def field_simps)
          using `?lslr \<ge> 0` by arith
      next
        case [simp]: True
        show ?thesis
        proof (cases l)
          case Leaf
          have 1: "log 2 (real (size r) + 2) \<ge> 0" by(simp)
          show ?thesis
            using Leaf opt apply(simp add: Splay_Tree.delete_def t_delete_def field_simps)
            using 1 `?lslr \<ge> 0` by arith
        next
          case (Node ll y lr)
          then obtain l' y' r' where [simp]:
            "splay_max (Node ll y lr) = Node l' y' r'"
            using splay_max_Leaf_iff tree.exhaust by blast
          have "bst l" using bst_splay[OF 5, of a] by simp
          have "\<Phi> r' \<ge> 0" apply (induction r') by (auto)
          have optm: "real(t_splay_max l) + \<Phi> (splay_max l) - \<Phi> l  \<le> 3 * \<phi> l + 1"
            using Am_ub3[OF `bst l`, simplified Am_def]
            by (simp add: field_simps Node)
          have 1: "log 2 (2+(real(size l')+real(size r))) \<le> log 2 (2+(real(size l)+real(size r)))"
            using size_splay_max[of l] Node by simp
          have 2: "log 2 (2 + (real (size l') + real (size r'))) \<ge> 0" by simp
          have 3: "log 2 (size1 l' + size1 r) \<le> log 2 (size1 l' + size1 r') + log 2 ?slr"
            apply simp using 1 2 by arith
          have 4: "log 2 (real(size ll) + (real(size lr) + 2)) \<le> ?lslr"
            using size_if_splay[OF sp] Node by simp
          show ?thesis using add_mono[OF opt optm] Node 3
            apply(simp add: Splay_Tree.delete_def t_delete_def field_simps)
            using 4 `\<Phi> r' \<ge> 0` by arith
        qed
      qed
    qed
  qed
qed

end
