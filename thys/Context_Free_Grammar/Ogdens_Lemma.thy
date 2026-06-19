section \<open>Ogden's Lemma for Context-Free Grammars\<close>

theory Ogdens_Lemma
imports
  "Context_Free_Grammar.Chomsky_Normal_Form"
  "Context_Free_Grammar.Parse_Tree"
begin

text \<open>
Ogden's Lemma \cite{Ogden68} (see also \cite{HopcroftU79}) is a refinement of the pumping lemma
in which one first \<^emph>\<open>marks\<close> (``distinguishes'') a set of positions of the word,
and the pumped parts are guaranteed to interact with the marked positions.

  Unlike the pumping lemma (theory \<open>Pumping_Lemma_CFG\<close>), whose proof
  follows a single path and therefore does \<^emph>\<open>not\<close> need explicit parse trees, Ogden's lemma
  is genuinely a parse-tree argument: a \<^emph>\<open>branch point\<close> is a node \<^emph>\<open>both\<close> of whose subtrees
  contain a marked leaf, and that notion cannot be expressed along one path only. We therefore
  build on theory \<open>Parse_Tree\<close>.

This theory was generated with the help of Claude and the above literature.
\<close>


subsection \<open>Markings\<close>

text \<open>A \<^emph>\<open>marking\<close> of a word/fringe is a boolean list of the same length; position \<open>i\<close> is
  distinguished iff the marking carries \<^const>\<open>True\<close> there. \<^term>\<open>dcount ms\<close> counts the
  distinguished positions in (a slice) \<open>ms\<close>.\<close>

abbreviation dcount :: "bool list \<Rightarrow> nat" where
"dcount ms \<equiv> count_list ms True"


subsection \<open>CNF parse trees and branch points\<close>

text \<open>\<^term>\<open>cnf_tree t\<close> characterises the shape of a complete parse tree of a terminal word
  under a CNF grammar: every internal node either has a single terminal-leaf child
  (\<open>A \<rightarrow> a\<close>) or two nonterminal-rooted subtrees (\<open>A \<rightarrow> B C\<close>); all leaves are terminals.\<close>

fun cnf_tree :: "('n,'t) ptree \<Rightarrow> bool" where
"cnf_tree (Sym (Tm _)) = True" |
"cnf_tree (Sym (Nt _)) = False" |
"cnf_tree (Prod _ [Sym (Tm _)]) = True" |
"cnf_tree (Prod _ [t1, t2]) =
   ((\<exists>B. root t1 = Nt B) \<and> (\<exists>C. root t2 = Nt C) \<and> cnf_tree t1 \<and> cnf_tree t2)" |
"cnf_tree (Prod _ _) = False"

text \<open>Following Hopcroft \& Ullman, descend from the root choosing, at each branch point, the
  subtree with more distinguished leaves (and otherwise the unique marked subtree). \<^term>\<open>bspine t ms\<close>
  collects the nonterminals labelling the \<^emph>\<open>branch points\<close> met on this ``heavy'' path, top to
  bottom. The marking \<^term>\<open>ms\<close> is the slice of the global marking aligned with \<^term>\<open>fringe t\<close>;
  a binary node splits it at \<^term>\<open>length (fringe t1)\<close>.\<close>

fun bspine :: "('n,'t) ptree \<Rightarrow> bool list \<Rightarrow> 'n list" where
"bspine (Prod A [t1, t2]) ms =
  (let ms1 = take (length (fringe t1)) ms; ms2 = drop (length (fringe t1)) ms in
     if 0 < dcount ms1 \<and> 0 < dcount ms2
       then A # (if dcount ms2 \<le> dcount ms1 then bspine t1 ms1 else bspine t2 ms2)
     else if 0 < dcount ms1 then bspine t1 ms1
     else bspine t2 ms2)" |
"bspine _ _ = []"

text \<open>\<^bold>\<open>Building block 1.\<close> A complete parse tree of a terminal word under a CNF grammar is a
  \<^const>\<open>cnf_tree\<close>. \<^emph>\<open>Proof:\<close> induction on \<open>t\<close>; \<^const>\<open>CNF\<close> forces \<open>(A, map root ts) \<in> P\<close> to be
  either \<open>[Tm a]\<close> or \<open>[Nt B, Nt C]\<close>, and \<^prop>\<open>fringe t = map Tm w\<close> forces every leaf to be a
  \<^const>\<open>Tm\<close>.\<close>

lemma cnf_tree_if_parse_tree:
  "\<lbrakk> CNF P; parse_tree P t; fringe t = map Tm w \<rbrakk> \<Longrightarrow> cnf_tree t"
proof (induction t arbitrary: w)
  case (Sym s) thus ?case by fastforce
next
  case (Prod A ts)
  have disj: "(\<exists>B C. map root ts = [Nt B, Nt C]) \<or> (\<exists>a. map root ts = [Tm a])"
    using Prod.prems(1,2) by (auto simp: CNF_def)
  then show ?case
  proof (elim disjE exE)
    fix B C assume "map root ts = [Nt B, Nt C]"
    then obtain t1 t2 where ts: "ts = [t1, t2]"
      and r1: "root t1 = Nt B" and r2: "root t2 = Nt C"
      by (auto simp: map_eq_Cons_conv)
    have "map Tm w = fringe t1 @ fringe t2" using Prod.prems(3) ts by simp
    then obtain w1 w2 where w12: "fringe t1 = map Tm w1" "fringe t2 = map Tm w2"
      by (auto simp: map_eq_append_conv)
    have "cnf_tree t1" "cnf_tree t2"
      using Prod.IH Prod.prems(1,2) ts w12 by auto
    thus "cnf_tree (Prod A ts)" using ts r1 r2 by auto
  next
    fix a assume "map root ts = [Tm a]"
    then obtain t' where t': "ts = [t']" and r: "root t' = Tm a"
      by (auto simp: map_eq_Cons_conv)
    from t' r have "ts = [Sym (Tm a)]" by (cases t') auto
    thus "cnf_tree (Prod A ts)" by simp
  qed
qed

text \<open>\<^bold>\<open>Building block 2.\<close> Each branch point at least halves the number of distinguished leaves
  on the heavy side, so a tree with \<open>d\<close> distinguished leaves has a heavy path with at least
  \<open>log2 d\<close> branch points. \<^emph>\<open>Proof:\<close> induction on \<open>t\<close>. At a binary node \<open>ms = ms1 @ ms2\<close> and
  \<^prop>\<open>dcount ms = dcount ms1 + dcount ms2\<close>; at a branch point we recurse into the heavier child
  \<open>h\<close>, with \<^prop>\<open>dcount ms \<le> 2 * dcount h\<close> and one more branch point; otherwise all marks lie in one
  child and the bound is preserved.\<close>

lemma dcount_aux: "length ms = Suc 0 \<Longrightarrow> dcount ms \<le> Suc 0"
  by (metis count_le_length)

lemma dcount_le_pow_bspine:
  "\<lbrakk> cnf_tree t; length ms = length (fringe t) \<rbrakk> \<Longrightarrow> dcount ms \<le> 2 ^ length (bspine t ms)"
proof (induction t arbitrary: ms rule: cnf_tree.induct)
  case (4 A t1 t2 ms)
  let ?n1 = "length (fringe t1)"
  let ?ms1 = "take ?n1 ms"
  let ?ms2 = "drop ?n1 ms"
  have ct1: "cnf_tree t1" and ct2: "cnf_tree t2" using "4.prems"(1) by auto
  have len: "length ms = length (fringe t1) + length (fringe t2)" using "4.prems"(2) by simp
  have l1: "length ?ms1 = length (fringe t1)" using len by simp
  have l2: "length ?ms2 = length (fringe t2)" using len by simp
  have dc: "dcount ms = dcount ?ms1 + dcount ?ms2"
    by (metis append_take_drop_id count_list_append)
  have IH1: "dcount ?ms1 \<le> 2 ^ length (bspine t1 ?ms1)" using "4.IH"(1) ct1 l1 by blast
  have IH2: "dcount ?ms2 \<le> 2 ^ length (bspine t2 ?ms2)" using "4.IH"(2) ct2 l2 by blast
  consider (both) "0 < dcount ?ms1 \<and> 0 < dcount ?ms2"
    | (left) "\<not> (0 < dcount ?ms1 \<and> 0 < dcount ?ms2)" "0 < dcount ?ms1"
    | (right) "\<not> (0 < dcount ?ms1 \<and> 0 < dcount ?ms2)" "\<not> 0 < dcount ?ms1"
    by blast
  then show ?case
  proof cases
    case both
    show ?thesis
    proof (cases "dcount ?ms2 \<le> dcount ?ms1")
      case True
      hence bs: "bspine (Prod A [t1, t2]) ms = A # bspine t1 ?ms1"
        using both by (simp add: Let_def)
      have "dcount ms \<le> 2 * dcount ?ms1" using dc True by simp
      also have "\<dots> \<le> 2 * 2 ^ length (bspine t1 ?ms1)" using IH1 by simp
      also have "\<dots> = 2 ^ length (bspine (Prod A [t1, t2]) ms)" using bs by simp
      finally show ?thesis .
    next
      case False
      hence bs: "bspine (Prod A [t1, t2]) ms = A # bspine t2 ?ms2"
        using both by (simp add: Let_def)
      have "dcount ms \<le> 2 * dcount ?ms2" using dc False by simp
      also have "\<dots> \<le> 2 * 2 ^ length (bspine t2 ?ms2)" using IH2 by simp
      also have "\<dots> = 2 ^ length (bspine (Prod A [t1, t2]) ms)" using bs by simp
      finally show ?thesis .
    qed
  next
    case left
    hence z2: "dcount ?ms2 = 0" by simp
    have bs: "bspine (Prod A [t1, t2]) ms = bspine t1 ?ms1"
      using left by (simp add: Let_def)
    have "dcount ms = dcount ?ms1" using dc z2 by simp
    also have "\<dots> \<le> 2 ^ length (bspine t1 ?ms1)" using IH1 by simp
    also have "\<dots> = 2 ^ length (bspine (Prod A [t1, t2]) ms)" using bs by simp
    finally show ?thesis .
  next
    case right
    hence z1: "dcount ?ms1 = 0" by simp
    have bs: "bspine (Prod A [t1, t2]) ms = bspine t2 ?ms2"
      using right by (simp add: Let_def)
    have "dcount ms = dcount ?ms2" using dc z1 by simp
    also have "\<dots> \<le> 2 ^ length (bspine t2 ?ms2)" using IH2 by simp
    also have "\<dots> = 2 ^ length (bspine (Prod A [t1, t2]) ms)" using bs by simp
    finally show ?thesis .
  qed
qed (simp_all add: dcount_aux)

text \<open>\<^bold>\<open>Building block 3.\<close> Every label on the spine is a left-hand side of \<open>P\<close>, hence a
  nonterminal of \<open>P\<close>. \<^emph>\<open>Proof:\<close> induction on \<open>t\<close>; a label \<open>A\<close> is emitted only at a
  \<^term>\<open>Prod A [t1,t2]\<close> node, where \<^prop>\<open>(A, [root t1, root t2]) \<in> P\<close>.\<close>

lemma bspine_in_Nts:
  "parse_tree P t \<Longrightarrow> set (bspine t ms) \<subseteq> Nts P"
proof (induction t arbitrary: ms rule: cnf_tree.induct)
  case (4 A t1 t2 ms)
  let ?ms1 = "take (length (fringe t1)) ms"
  let ?ms2 = "drop (length (fringe t1)) ms"
  have pt1: "parse_tree P t1" and pt2: "parse_tree P t2"
    and inP: "(A, [root t1, root t2]) \<in> P" using "4.prems" by auto
  have A: "A \<in> Nts P" using inP by (auto simp: Nts_def)
  have s1: "set (bspine t1 ?ms1) \<subseteq> Nts P" using "4.IH"(1) pt1 by blast
  have s2: "set (bspine t2 ?ms2) \<subseteq> Nts P" using "4.IH"(2) pt2 by blast
  have "set (bspine (Prod A [t1, t2]) ms)
        \<subseteq> insert A (set (bspine t1 ?ms1) \<union> set (bspine t2 ?ms2))"
    by (auto simp: Let_def)
  thus ?case using A s1 s2 by auto
qed simp_all

subsection \<open>Locating a labelled branch point and lifting through a CNF node\<close>

lemma derives_bin:
  assumes "(A0, [Nt B, Nt C]) \<in> P" "P \<turnstile> [Nt B] \<Rightarrow>* \<alpha>" "P \<turnstile> [Nt C] \<Rightarrow>* \<beta>"
  shows "P \<turnstile> [Nt A0] \<Rightarrow>* \<alpha> @ \<beta>"
using derives_append_append[OF assms(2,3)]
by (simp add: derives_Cons_rule[OF assms(1)])


text \<open>If \<open>A\<close> labels a branch point on the heavy path of \<open>t\<close>, read off the context derivation
  \<open>[root t] \<Rightarrow>* v [Nt A] x\<close> and the subterminal yield \<open>[Nt A] \<Rightarrow>* w\<close>, threading the marking.\<close>

lemma ctx_label:
  "\<lbrakk> cnf_tree t;  parse_tree P t;  length ms = length (fringe t);  fringe t = map Tm zt;
     A \<in> set (bspine t ms) \<rbrakk> \<Longrightarrow>
   \<exists>v w x dv dw dx. zt = v @ w @ x \<and> ms = dv @ dw @ dx \<and>
     length dv = length v \<and> length dw = length w \<and> length dx = length x \<and>
     P \<turnstile> [root t] \<Rightarrow>* map Tm v @ [Nt A] @ map Tm x \<and> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
proof (induction t arbitrary: ms zt rule: cnf_tree.induct)
  case (4 A0 t1 t2 ms zt)
  from "4.prems"(1) obtain B C where rB: "root t1 = Nt B" and rC: "root t2 = Nt C"
    and ct1: "cnf_tree t1" and ct2: "cnf_tree t2" by auto
  from "4.prems"(2) have pt1: "parse_tree P t1" and pt2: "parse_tree P t2"
    and inP: "(A0, [root t1, root t2]) \<in> P" by auto
  have inP': "(A0, [Nt B, Nt C]) \<in> P" using inP rB rC by simp
  let ?n1 = "length (fringe t1)"
  let ?ms1 = "take ?n1 ms"
  let ?ms2 = "drop ?n1 ms"
  have len: "length ms = length (fringe t1) + length (fringe t2)" using "4.prems"(3) by simp
  have l1: "length ?ms1 = length (fringe t1)" and l2: "length ?ms2 = length (fringe t2)"
    using len by auto
  have msplit: "ms = ?ms1 @ ?ms2" by simp
  from "4.prems"(4) have "map Tm zt = fringe t1 @ fringe t2" by simp
  then obtain z1 z2 where z1: "fringe t1 = map Tm z1" and z2: "fringe t2 = map Tm z2"
    and zt: "zt = z1 @ z2" by (auto simp: map_eq_append_conv)
  have dB: "P \<turnstile> [Nt B] \<Rightarrow>* map Tm z1" using derives_fringe_if_parse_tree[OF pt1] rB z1 by simp
  have dC: "P \<turnstile> [Nt C] \<Rightarrow>* map Tm z2" using derives_fringe_if_parse_tree[OF pt2] rC z2 by simp
  have recL: ?case if AL: "A \<in> set (bspine t1 ?ms1)"
  proof -
    from "4.IH"(1)[OF ct1 pt1 l1 z1 AL] obtain v1 w1 x1 dv1 dw1 dx1 where
      Q: "z1 = v1 @ w1 @ x1" "?ms1 = dv1 @ dw1 @ dx1"
         "length dv1 = length v1" "length dw1 = length w1" "length dx1 = length x1"
         "P \<turnstile> [root t1] \<Rightarrow>* map Tm v1 @ [Nt A] @ map Tm x1" "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w1" by blast
    have dB1: "P \<turnstile> [Nt B] \<Rightarrow>* map Tm v1 @ [Nt A] @ map Tm x1" using Q(6) rB by simp
    have "P \<turnstile> [Nt A0] \<Rightarrow>* (map Tm v1 @ [Nt A] @ map Tm x1) @ map Tm z2"
      by (rule derives_bin[OF inP' dB1 dC])
    hence d: "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm v1 @ [Nt A] @ map Tm (x1 @ z2)" by simp
    have "zt = v1 @ w1 @ (x1 @ z2) \<and> ms = dv1 @ dw1 @ (dx1 @ ?ms2) \<and>
          length dv1 = length v1 \<and> length dw1 = length w1 \<and>
          length (dx1 @ ?ms2) = length (x1 @ z2) \<and>
          P \<turnstile> [root (Prod A0 [t1,t2])] \<Rightarrow>* map Tm v1 @ [Nt A] @ map Tm (x1 @ z2) \<and>
          P \<turnstile> [Nt A] \<Rightarrow>* map Tm w1"
      using Q zt z2 l2 d msplit by simp
    thus ?case by blast
  qed
  have recR: ?case if AR: "A \<in> set (bspine t2 ?ms2)"
  proof -
    from "4.IH"(2)[OF ct2 pt2 l2 z2 AR] obtain v2 w2 x2 dv2 dw2 dx2 where
      Q: "z2 = v2 @ w2 @ x2" "?ms2 = dv2 @ dw2 @ dx2"
         "length dv2 = length v2" "length dw2 = length w2" "length dx2 = length x2"
         "P \<turnstile> [root t2] \<Rightarrow>* map Tm v2 @ [Nt A] @ map Tm x2" "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w2" by blast
    have dC2: "P \<turnstile> [Nt C] \<Rightarrow>* map Tm v2 @ [Nt A] @ map Tm x2" using Q(6) rC by simp
    have "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm z1 @ (map Tm v2 @ [Nt A] @ map Tm x2)"
      by (rule derives_bin[OF inP' dB dC2])
    hence d: "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm (z1 @ v2) @ [Nt A] @ map Tm x2" by simp
    have "zt = (z1 @ v2) @ w2 @ x2 \<and> ms = (?ms1 @ dv2) @ dw2 @ dx2 \<and>
          length (?ms1 @ dv2) = length (z1 @ v2) \<and> length dw2 = length w2 \<and>
          length dx2 = length x2 \<and>
          P \<turnstile> [root (Prod A0 [t1,t2])] \<Rightarrow>* map Tm (z1 @ v2) @ [Nt A] @ map Tm x2 \<and>
          P \<turnstile> [Nt A] \<Rightarrow>* map Tm w2"
      using Q zt z1 l1 d msplit by simp
    thus ?case by blast
  qed
  have lenzt: "length ms = length zt" using "4.prems"(3,4) by (metis length_map)
  show ?case
  proof (cases "A = A0 \<and> 0 < dcount ?ms1 \<and> 0 < dcount ?ms2")
    case True
    hence rt: "root (Prod A0 [t1,t2]) = Nt A" by simp
    have D1: "P \<turnstile> [root (Prod A0 [t1,t2])] \<Rightarrow>* map Tm [] @ [Nt A] @ map Tm []"
      using rt by simp
    have D2: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm zt"
      using derives_fringe_if_parse_tree[OF "4.prems"(2)] "4.prems"(4) rt by simp
    show ?thesis using D1 D2 lenzt
      by (metis append.right_neutral append_Nil list.size(3))
  next
    case False
    hence "A \<in> set (bspine t1 ?ms1) \<or> A \<in> set (bspine t2 ?ms2)"
      using "4.prems"(5) by (auto simp: Let_def split: if_splits)
    thus ?thesis using recL recR by blast
  qed
qed simp_all


text \<open>Descend the heavy path to the \<^emph>\<open>lowest\<close> repeated branch-point label, lifting the
  decomposition through each CNF node. When the heavy child's spine is already distinct, the
  repeat is the current label, and the bound \<open>2 ^ (card (Nts P) + 1)\<close> holds because a distinct
  spine has at most \<open>card (Nts P)\<close> labels.\<close>

lemma ogden_extract:
  "\<lbrakk> cnf_tree t;  parse_tree P t;  length ms = length (fringe t);  fringe t = map Tm zt;
    finite P; \<not> distinct (bspine t ms) \<rbrakk> \<Longrightarrow>
   \<exists>A u v w x y du dv dw dx dy. A \<in> Nts P \<and>
     zt = u @ v @ w @ x @ y \<and> ms = du @ dv @ dw @ dx @ dy \<and>
     length du = length u \<and> length dv = length v \<and> length dw = length w \<and>
       length dx = length x \<and> length dy = length y \<and>
     P \<turnstile> [root t] \<Rightarrow>* map Tm u @ [Nt A] @ map Tm y \<and>
     P \<turnstile> [Nt A] \<Rightarrow>* map Tm v @ [Nt A] @ map Tm x \<and>
     P \<turnstile> [Nt A] \<Rightarrow>* map Tm w \<and>
     1 \<le> dcount (dv @ dx) \<and> dcount (dv @ dw @ dx) \<le> 2 ^ (card (Nts P) + 1)"
proof (induction t arbitrary: ms zt rule: cnf_tree.induct)
  case (4 A0 t1 t2 ms zt)
  from "4.prems"(1) obtain B C where rB: "root t1 = Nt B" and rC: "root t2 = Nt C"
    and ct1: "cnf_tree t1" and ct2: "cnf_tree t2" by auto
  from "4.prems"(2) have pt1: "parse_tree P t1" and pt2: "parse_tree P t2"
    and inP: "(A0, [root t1, root t2]) \<in> P" by auto
  have inP': "(A0, [Nt B, Nt C]) \<in> P" using inP rB rC by simp
  have A0Nts: "A0 \<in> Nts P" using inP by (auto simp: Nts_def)
  let ?n1 = "length (fringe t1)"
  let ?ms1 = "take ?n1 ms"
  let ?ms2 = "drop ?n1 ms"
  have len: "length ms = length (fringe t1) + length (fringe t2)" using "4.prems"(3) by simp
  have l1: "length ?ms1 = length (fringe t1)" and l2: "length ?ms2 = length (fringe t2)"
    using len by auto
  have msplit: "ms = ?ms1 @ ?ms2" by simp
  from "4.prems"(4) have "map Tm zt = fringe t1 @ fringe t2" by simp
  then obtain z1 z2 where z1: "fringe t1 = map Tm z1" and z2: "fringe t2 = map Tm z2"
    and zt: "zt = z1 @ z2" by (auto simp: map_eq_append_conv)
  have dB: "P \<turnstile> [Nt B] \<Rightarrow>* map Tm z1" using derives_fringe_if_parse_tree[OF pt1] rB z1 by simp
  have dC: "P \<turnstile> [Nt C] \<Rightarrow>* map Tm z2" using derives_fringe_if_parse_tree[OF pt2] rC z2 by simp
  \<comment> \<open>recurse into the left child\<close>
  have recurseL: ?case if D: "\<not> distinct (bspine t1 ?ms1)"
  proof -
    from "4.IH"(1)[OF ct1 pt1 l1 z1 "4.prems"(5) D] obtain A u1 v1 w1 x1 y1 du1 dv1 dw1 dx1 dy1
      where Q: "A \<in> Nts P" "z1 = u1 @ v1 @ w1 @ x1 @ y1" "?ms1 = du1 @ dv1 @ dw1 @ dx1 @ dy1"
        "length du1 = length u1" "length dv1 = length v1" "length dw1 = length w1"
        "length dx1 = length x1" "length dy1 = length y1"
        "P \<turnstile> [root t1] \<Rightarrow>* map Tm u1 @ [Nt A] @ map Tm y1"
        "P \<turnstile> [Nt A] \<Rightarrow>* map Tm v1 @ [Nt A] @ map Tm x1" "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w1"
        "1 \<le> dcount (dv1 @ dx1)" "dcount (dv1 @ dw1 @ dx1) \<le> 2 ^ (card (Nts P) + 1)" by blast
    have dBu: "P \<turnstile> [Nt B] \<Rightarrow>* map Tm u1 @ [Nt A] @ map Tm y1" using Q(9) rB by simp
    have "P \<turnstile> [Nt A0] \<Rightarrow>* (map Tm u1 @ [Nt A] @ map Tm y1) @ map Tm z2"
      by (rule derives_bin[OF inP' dBu dC])
    hence d: "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm u1 @ [Nt A] @ map Tm (y1 @ z2)" by simp
    have "A \<in> Nts P \<and> zt = u1 @ v1 @ w1 @ x1 @ (y1 @ z2) \<and>
          ms = du1 @ dv1 @ dw1 @ dx1 @ (dy1 @ ?ms2) \<and>
          length du1 = length u1 \<and> length dv1 = length v1 \<and> length dw1 = length w1 \<and>
          length dx1 = length x1 \<and> length (dy1 @ ?ms2) = length (y1 @ z2) \<and>
          P \<turnstile> [root (Prod A0 [t1,t2])] \<Rightarrow>* map Tm u1 @ [Nt A] @ map Tm (y1 @ z2) \<and>
          P \<turnstile> [Nt A] \<Rightarrow>* map Tm v1 @ [Nt A] @ map Tm x1 \<and> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w1 \<and>
          1 \<le> dcount (dv1 @ dx1) \<and> dcount (dv1 @ dw1 @ dx1) \<le> 2 ^ (card (Nts P) + 1)"
      using Q zt z2 l2 d msplit by simp
    thus ?case by blast
  qed
  \<comment> \<open>recurse into the right child\<close>
  have recurseR: ?case if D: "\<not> distinct (bspine t2 ?ms2)"
  proof -
    from "4.IH"(2)[OF ct2 pt2 l2 z2 "4.prems"(5) D] obtain A u2 v2 w2 x2 y2 du2 dv2 dw2 dx2 dy2
      where Q: "A \<in> Nts P" "z2 = u2 @ v2 @ w2 @ x2 @ y2" "?ms2 = du2 @ dv2 @ dw2 @ dx2 @ dy2"
        "length du2 = length u2" "length dv2 = length v2" "length dw2 = length w2"
        "length dx2 = length x2" "length dy2 = length y2"
        "P \<turnstile> [root t2] \<Rightarrow>* map Tm u2 @ [Nt A] @ map Tm y2"
        "P \<turnstile> [Nt A] \<Rightarrow>* map Tm v2 @ [Nt A] @ map Tm x2" "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w2"
        "1 \<le> dcount (dv2 @ dx2)" "dcount (dv2 @ dw2 @ dx2) \<le> 2 ^ (card (Nts P) + 1)" by blast
    have dCu: "P \<turnstile> [Nt C] \<Rightarrow>* map Tm u2 @ [Nt A] @ map Tm y2" using Q(9) rC by simp
    have "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm z1 @ (map Tm u2 @ [Nt A] @ map Tm y2)"
      by (rule derives_bin[OF inP' dB dCu])
    hence d: "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm (z1 @ u2) @ [Nt A] @ map Tm y2" by simp
    have "A \<in> Nts P \<and> zt = (z1 @ u2) @ v2 @ w2 @ x2 @ y2 \<and>
          ms = (?ms1 @ du2) @ dv2 @ dw2 @ dx2 @ dy2 \<and>
          length (?ms1 @ du2) = length (z1 @ u2) \<and> length dv2 = length v2 \<and>
          length dw2 = length w2 \<and> length dx2 = length x2 \<and> length dy2 = length y2 \<and>
          P \<turnstile> [root (Prod A0 [t1,t2])] \<Rightarrow>* map Tm (z1 @ u2) @ [Nt A] @ map Tm y2 \<and>
          P \<turnstile> [Nt A] \<Rightarrow>* map Tm v2 @ [Nt A] @ map Tm x2 \<and> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w2 \<and>
          1 \<le> dcount (dv2 @ dx2) \<and> dcount (dv2 @ dw2 @ dx2) \<le> 2 ^ (card (Nts P) + 1)"
      using Q zt z1 l1 d msplit by simp
    thus ?case by blast
  qed
  \<comment> \<open>the current node is the upper repeated node; locate the lower one in child \<open>tc\<close>\<close>
  have top: ?case
    if heavy: "bspine (Prod A0 [t1,t2]) ms = A0 # bspine tc mc"
    and DI: "distinct (bspine tc mc)" and AIN: "A0 \<in> set (bspine tc mc)"
    and tc: "tc = t1 \<and> mc = ?ms1 \<and> od = ?ms2 \<and> co = z2 \<or> tc = t2 \<and> mc = ?ms2 \<and> od = ?ms1 \<and> co = z1"
    and ctc: "cnf_tree tc" and ptc: "parse_tree P tc"
    and lc: "length mc = length (fringe tc)" and zc: "fringe tc = map Tm zc"
    and side: "0 < dcount od"
    and ctxbin: "\<And>v1 x1. P \<turnstile> [root tc] \<Rightarrow>* map Tm v1 @ [Nt A0] @ map Tm x1
                  \<Longrightarrow> P \<turnstile> [Nt A0] \<Rightarrow>* map Tm (v @ v1) @ [Nt A0] @ map Tm (x1 @ x)"
    and split: "zt = v @ zc @ x \<and> ms = dv @ mc @ dx \<and> length dv = length v \<and> length dx = length x
                \<and> dcount (dv @ dx) = dcount od"
  for tc mc od co zc v x dv dx
  proof -
    from ctx_label[OF ctc ptc lc zc AIN] obtain v1 w1 x1 dv1 dw1 dx1 where
      Q: "zc = v1 @ w1 @ x1" "mc = dv1 @ dw1 @ dx1"
         "length dv1 = length v1" "length dw1 = length w1" "length dx1 = length x1"
         "P \<turnstile> [root tc] \<Rightarrow>* map Tm v1 @ [Nt A0] @ map Tm x1" "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm w1" by blast
    have dctx: "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm (v @ v1) @ [Nt A0] @ map Tm (x1 @ x)"
      by (rule ctxbin[OF Q(6)])
    have fin: "finite (Nts P)" using "4.prems"(5) by (rule finite_Nts)
    have dwms: "dcount ((dv @ dv1) @ dw1 @ (dx1 @ dx)) = dcount ms"
      using split Q(2) by (simp)
    have bound: "dcount ms \<le> 2 ^ (card (Nts P) + 1)"
    proof -
      have "card (set (bspine tc mc)) \<le> card (Nts P)"
        by (rule card_mono[OF fin bspine_in_Nts[OF ptc]])
      hence le: "length (bspine tc mc) \<le> card (Nts P)" using DI distinct_card by fastforce
      have "dcount ms \<le> 2 ^ length (bspine (Prod A0 [t1,t2]) ms)"
        by (rule dcount_le_pow_bspine[OF "4.prems"(1) "4.prems"(3)])
      also have "\<dots> = 2 ^ (length (bspine tc mc) + 1)" using heavy by simp
      also have "\<dots> \<le> 2 ^ (card (Nts P) + 1)" using le by simp
      finally show ?thesis .
    qed
    have sidefull: "1 \<le> dcount ((dv @ dv1) @ (dx1 @ dx))"
      using less_eq_Suc_le side split by auto
    have "A0 \<in> Nts P \<and> zt = (v @ v1) @ w1 @ (x1 @ x) @ [] \<and>
          ms = (dv @ dv1) @ dw1 @ (dx1 @ dx) @ [] \<and>
          length (dv @ dv1) = length (v @ v1) \<and> length dw1 = length w1 \<and>
          length (dx1 @ dx) = length (x1 @ x) \<and> length ([]::bool list) = length ([]::'b list) \<and>
          P \<turnstile> [root (Prod A0 [t1,t2])] \<Rightarrow>* map Tm [] @ [Nt A0] @ map Tm [] \<and>
          P \<turnstile> [Nt A0] \<Rightarrow>* map Tm (v @ v1) @ [Nt A0] @ map Tm (x1 @ x) \<and>
          P \<turnstile> [Nt A0] \<Rightarrow>* map Tm w1 \<and>
          1 \<le> dcount ((dv @ dv1) @ (dx1 @ dx)) \<and>
          dcount ((dv @ dv1) @ dw1 @ (dx1 @ dx)) \<le> 2 ^ (card (Nts P) + 1)"
      using A0Nts split Q(1) Q(2) Q(3) Q(4) Q(5) dctx Q(7) sidefull dwms bound by simp
    thus ?case by blast
  qed
  show ?case
  proof (cases "0 < dcount ?ms1 \<and> 0 < dcount ?ms2")
    case bpc: True
    show ?thesis
    proof (cases "dcount ?ms2 \<le> dcount ?ms1")
      case hl: True
      have sp: "bspine (Prod A0 [t1,t2]) ms = A0 # bspine t1 ?ms1" using bpc hl by (simp add: Let_def)
      show ?thesis
      proof (cases "distinct (bspine t1 ?ms1)")
        case True
        hence AIN: "A0 \<in> set (bspine t1 ?ms1)" using "4.prems"(6) sp by auto
        show ?thesis
        proof (rule top[where tc = t1 and mc = ?ms1 and od = ?ms2 and co = z2 and zc = z1
                          and v = "[]" and x = z2 and dv = "[]" and dx = ?ms2])
          show "\<And>v1 x1. P \<turnstile> [root t1] \<Rightarrow>* map Tm v1 @ [Nt A0] @ map Tm x1
                \<Longrightarrow> P \<turnstile> [Nt A0] \<Rightarrow>* map Tm ([] @ v1) @ [Nt A0] @ map Tm (x1 @ z2)"
          proof -
            fix v1 x1 assume "P \<turnstile> [root t1] \<Rightarrow>* map Tm v1 @ [Nt A0] @ map Tm x1"
            hence "P \<turnstile> [Nt B] \<Rightarrow>* map Tm v1 @ [Nt A0] @ map Tm x1" using rB by simp
            from derives_bin[OF inP' this dC]
            show "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm ([] @ v1) @ [Nt A0] @ map Tm (x1 @ z2)" by simp
          qed
          show "zt = [] @ z1 @ z2 \<and> ms = [] @ ?ms1 @ ?ms2 \<and> length ([]::bool list) = length ([]::'b list)
                \<and> length ?ms2 = length z2 \<and> dcount ([] @ ?ms2) = dcount ?ms2"
            using zt msplit l2 z2 by simp
          show "0 < dcount ?ms2" using bpc by simp
        qed (use sp True AIN ct1 pt1 l1 z1 in simp_all)
      next
        case False thus ?thesis by (rule recurseL)
      qed
    next
      case hr: False
      have sp: "bspine (Prod A0 [t1,t2]) ms = A0 # bspine t2 ?ms2" using bpc hr by (simp add: Let_def)
      show ?thesis
      proof (cases "distinct (bspine t2 ?ms2)")
        case True
        hence AIN: "A0 \<in> set (bspine t2 ?ms2)" using "4.prems"(6) sp by auto
        show ?thesis
        proof (rule top[where tc = t2 and mc = ?ms2 and od = ?ms1 and co = z1 and zc = z2
                          and v = z1 and x = "[]" and dv = ?ms1 and dx = "[]"])
          show "\<And>v1 x1. P \<turnstile> [root t2] \<Rightarrow>* map Tm v1 @ [Nt A0] @ map Tm x1
                \<Longrightarrow> P \<turnstile> [Nt A0] \<Rightarrow>* map Tm (z1 @ v1) @ [Nt A0] @ map Tm (x1 @ [])"
          proof -
            fix v1 x1 assume "P \<turnstile> [root t2] \<Rightarrow>* map Tm v1 @ [Nt A0] @ map Tm x1"
            hence "P \<turnstile> [Nt C] \<Rightarrow>* map Tm v1 @ [Nt A0] @ map Tm x1" using rC by simp
            from derives_bin[OF inP' dB this]
            show "P \<turnstile> [Nt A0] \<Rightarrow>* map Tm (z1 @ v1) @ [Nt A0] @ map Tm (x1 @ [])" by simp
          qed
          show "zt = z1 @ z2 @ [] \<and> ms = ?ms1 @ ?ms2 @ [] \<and> length ?ms1 = length z1
                \<and> length ([]::bool list) = length ([]::'b list) \<and> dcount (?ms1 @ []) = dcount ?ms1"
            using zt msplit l1 z1 by simp
          show "0 < dcount ?ms1" using bpc by simp
        qed (use sp True AIN ct2 pt2 l2 z2 in simp_all)
      next
        case False thus ?thesis by (rule recurseR)
      qed
    qed
  next
    case nbp: False
    show ?thesis
    proof (cases "0 < dcount ?ms1")
      case True thus ?thesis
        using "4.prems"(6) nbp recurseL by auto
    next
      case False thus ?thesis
        using "4.prems"(6) recurseR by fastforce
    qed
  qed
qed simp_all


subsection \<open>The combinatorial core: extracting a pumpable nonterminal\<close>

text \<open>\<^bold>\<open>The heart of Ogden's lemma\<close> (Hopcroft \& Ullman, Ch.\ 6). Given a CNF grammar and a
  marking with at least \<open>2 ^ (card (Nts P) + 1)\<close> distinguished positions, we extract a
  nonterminal \<open>A\<close> and a decomposition \<open>z = u v w x y\<close> together with the three derivations that
  drive the pumping, plus the two marking conditions.

  \<^bold>\<open>Proof.\<close> From \<^prop>\<open>z \<in> Lang P S\<close> take a parse tree \<open>t\<close> (via @{thm [source] parse_tree_if_derives});
  it is a \<^const>\<open>cnf_tree\<close> by \<open>cnf_tree_if_parse_tree\<close>. By \<open>dcount_le_pow_bspine\<close>,
  \<^prop>\<open>dcount ds \<le> 2 ^ length (bspine t ds)\<close>, so with \<open>big\<close> the heavy path carries more than
  \<open>card (Nts P)\<close> branch-point labels; since these lie in \<open>Nts P\<close> (\<open>bspine_in_Nts\<close>) and \<open>Nts P\<close>
  has only \<open>card (Nts P)\<close> elements, the spine \<open>bspine t ds\<close> cannot be distinct. The branch-point
  extraction \<open>ogden_extract\<close> then descends the heavy path to the \<^bold>\<open>lowest\<close> repeated label,
  reading off the decomposition together with \<^prop>\<open>1 \<le> dcount (dv @ dx)\<close> and the bound
  \<^prop>\<open>dcount (dv @ dw @ dx) \<le> 2 ^ (card (Nts P) + 1)\<close> (the latter because the child spine below
  the repeat is distinct, hence of length \<open>\<le> card (Nts P)\<close>). Finally \<^prop>\<open>root t = Nt S\<close> turns
  the extracted context derivation into one from \<open>[Nt S]\<close>.\<close>

lemma ogden_split:
  assumes P: "CNF P" "finite P" and z: "z \<in> Lang P S"
    and ds: "length ds = length z"
    and big: "2 ^ (card (Nts P) + 1) \<le> dcount ds"
  shows "\<exists>A u v w x y du dv dw dx dy.
      A \<in> Nts P \<and>
      z = u @ v @ w @ x @ y \<and> ds = du @ dv @ dw @ dx @ dy \<and>
      length du = length u \<and> length dv = length v \<and> length dw = length w \<and>
        length dx = length x \<and> length dy = length y \<and>
      P \<turnstile> [Nt S] \<Rightarrow>* map Tm u @ [Nt A] @ map Tm y \<and>
      P \<turnstile> [Nt A] \<Rightarrow>* map Tm v @ [Nt A] @ map Tm x \<and>
      P \<turnstile> [Nt A] \<Rightarrow>* map Tm w \<and>
      1 \<le> dcount (dv @ dx) \<and>
      dcount (dv @ dw @ dx) \<le> 2 ^ (card (Nts P) + 1)"
proof -
  from z have derz: "P \<turnstile> [Nt S] \<Rightarrow>* map Tm z" by (simp add: Lang_def)
  from parse_tree_if_derives[OF derz]
  obtain t where t: "parse_tree P t \<and> fringe t = map Tm z \<and> root t = Nt S" ..
  hence pt: "parse_tree P t" and fr: "fringe t = map Tm z" and rt: "root t = Nt S" by auto
  have ct: "cnf_tree t" by (rule cnf_tree_if_parse_tree[OF P(1) pt fr])
  have len: "length ds = length (fringe t)" using ds fr by simp
  have dpow: "dcount ds \<le> 2 ^ length (bspine t ds)" by (rule dcount_le_pow_bspine[OF ct len])
  have nd: "\<not> distinct (bspine t ds)"
  proof
    assume D: "distinct (bspine t ds)"
    have "length (bspine t ds) = card (set (bspine t ds))" using D by (simp add: distinct_card)
    also have "\<dots> \<le> card (Nts P)"
      by (rule card_mono[OF finite_Nts[OF P(2)] bspine_in_Nts[OF pt]])
    finally have le: "length (bspine t ds) \<le> card (Nts P)" .
    have "(2::nat) ^ (card (Nts P) + 1) \<le> dcount ds" using big .
    also have "dcount ds \<le> 2 ^ length (bspine t ds)" using dpow .
    also have "\<dots> \<le> 2 ^ card (Nts P)" by (rule power_increasing[OF le]) simp
    finally show False by simp
  qed
  from ogden_extract[OF ct pt len fr P(2) nd]
  obtain A u v w x y du dv dw dx dy where
    Q: "A \<in> Nts P" "z = u @ v @ w @ x @ y" "ds = du @ dv @ dw @ dx @ dy"
       "length du = length u" "length dv = length v" "length dw = length w"
       "length dx = length x" "length dy = length y"
       "P \<turnstile> [root t] \<Rightarrow>* map Tm u @ [Nt A] @ map Tm y"
       "P \<turnstile> [Nt A] \<Rightarrow>* map Tm v @ [Nt A] @ map Tm x"
       "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
       "1 \<le> dcount (dv @ dx)" "dcount (dv @ dw @ dx) \<le> 2 ^ (card (Nts P) + 1)"
    by blast
  have S: "P \<turnstile> [Nt S] \<Rightarrow>* map Tm u @ [Nt A] @ map Tm y" using Q(9) rt by simp
  show ?thesis using Q S by blast
qed


subsection \<open>Derivation-level pumping\<close>

text \<open>Once the nonterminal \<open>A\<close> and its contexts have been extracted, the actual pumping is a
  pure derivation argument with no further reference to parse trees, exactly as in the
  inherent-ambiguity development.\<close>

lemma pump_derives:
  assumes S: "P \<turnstile> [Nt S] \<Rightarrow>* map Tm u @ [Nt A] @ map Tm y"
    and V: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm v @ [Nt A] @ map Tm x"
    and W: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
  shows "u @ v ^^ i @ w @ x ^^ i @ y \<in> Lang P S"
proof -
  have inner: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm (v ^^ i) @ [Nt A] @ map Tm (x ^^ i)" for i
  proof (induction i)
    case 0 show ?case by simp
  next
    case (Suc i)
    have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm (v ^^ i) @ (map Tm v @ [Nt A] @ map Tm x) @ map Tm (x ^^ i)"
      using Suc.IH derives_embed[OF V, of "map Tm (v ^^ i)" "map Tm (x ^^ i)"]
      by (meson rtranclp_trans)
    thus ?case
      by (metis append.assoc map_append pow_list_Suc pow_list_Suc2)
  qed
  have mid: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm (v ^^ i) @ map Tm w @ map Tm (x ^^ i)"
    using inner derives_embed[OF W, of "map Tm (v ^^ i)" "map Tm (x ^^ i)"]
    by (meson rtranclp_trans)
  have "P \<turnstile> [Nt S] \<Rightarrow>* map Tm u @ (map Tm (v ^^ i) @ map Tm w @ map Tm (x ^^ i)) @ map Tm y"
    using S derives_embed[OF mid, of "map Tm u" "map Tm y"]
    by (meson rtranclp_trans)
  hence "P \<turnstile> [Nt S] \<Rightarrow>* map Tm (u @ v ^^ i @ w @ x ^^ i @ y)"
    by simp
  thus ?thesis by (simp add: Lang_def)
qed


subsection \<open>Assembling Ogden's lemma\<close>

text \<open>The ``inner'' Ogden lemma for a CNF grammar: \<open>2 ^ (card (Nts P) + 1)\<close> distinguished
  positions force a marked pumpable decomposition.\<close>

lemma inner_ogden:
  assumes P: "CNF P" "finite P" and z: "z \<in> Lang P S"
    and ds: "length ds = length z"
    and big: "2 ^ (card (Nts P) + 1) \<le> dcount ds"
  shows "\<exists>u v w x y du dv dw dx dy.
      z = u @ v @ w @ x @ y \<and> ds = du @ dv @ dw @ dx @ dy \<and>
      length du = length u \<and> length dv = length v \<and> length dw = length w \<and>
        length dx = length x \<and> length dy = length y \<and>
      1 \<le> dcount (dv @ dx) \<and> dcount (dv @ dw @ dx) \<le> 2 ^ (card (Nts P) + 1) \<and>
      (\<forall>i. u @ v ^^ i @ w @ x ^^ i @ y \<in> Lang P S)"
proof -
  from ogden_split[OF P z ds big] obtain A u v w x y du dv dw dx dy where
    sp: "z = u @ v @ w @ x @ y" "ds = du @ dv @ dw @ dx @ dy"
        "length du = length u" "length dv = length v" "length dw = length w"
        "length dx = length x" "length dy = length y"
        "P \<turnstile> [Nt S] \<Rightarrow>* map Tm u @ [Nt A] @ map Tm y"
        "P \<turnstile> [Nt A] \<Rightarrow>* map Tm v @ [Nt A] @ map Tm x"
        "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        "1 \<le> dcount (dv @ dx)" "dcount (dv @ dw @ dx) \<le> 2 ^ (card (Nts P) + 1)"
    by blast
  have "\<forall>i. u @ v ^^ i @ w @ x ^^ i @ y \<in> Lang P S"
    using pump_derives[OF sp(8) sp(9) sp(10)] by blast
  with sp show ?thesis by blast
qed

text \<open>\<^term>\<open>ogden_property L n\<close> is the conclusion of Ogden's lemma for a language \<open>L\<close> with
  constant \<open>n\<close>: any word marked in \<open>n\<close> or more positions splits as \<open>u v w x y\<close> with the marking
  conditions and the pumping property. The marking is carried as a boolean list parallel to the
  word; \<open>dv @ dx\<close> and \<open>dv @ dw @ dx\<close> are the markings of \<open>v x\<close> and \<open>v w x\<close>.\<close>

abbreviation ogden_property :: "'t list set \<Rightarrow> nat \<Rightarrow> bool" where
"ogden_property L n \<equiv>
  (\<forall>z \<in> L. \<forall>ds. length ds = length z \<and> n \<le> dcount ds \<longrightarrow>
     (\<exists>u v w x y du dv dw dx dy.
        z = u @ v @ w @ x @ y \<and> ds = du @ dv @ dw @ dx @ dy \<and>
        length du = length u \<and> length dv = length v \<and> length dw = length w \<and>
          length dx = length x \<and> length dy = length y \<and>
        1 \<le> dcount (dv @ dx) \<and> dcount (dv @ dw @ dx) \<le> n \<and>
        (\<forall>i. u @ v ^^ i @ w @ x ^^ i @ y \<in> L)))"

theorem Ogden_Lemma_CNF:
  assumes "CNF P" "finite P"
  shows "\<exists>n. ogden_property (Lang P S) n"
proof
  show "ogden_property (Lang P S) (2 ^ (card (Nts P) + 1))"
    using inner_ogden[OF assms] by blast
qed

text \<open>For an arbitrary (finite) grammar we pass to a CNF grammar with the same language modulo
  the empty word (@{thm [source] cnf_exists}); the empty word carries no marks, so bumping the
  constant by one excludes it, exactly as in \<open>Pumping_Lemma\<close>.\<close>

theorem Ogden_Lemma:
  assumes "finite (P :: ('n::fresh0,'t) Prods)"
  shows "\<exists>n. ogden_property (Lang P S) n"
proof -
  obtain P' :: "('n,'t) Prods" where P':
    "finite P'" "CNF P'" "Lang P' S = Lang P S - {[]}"
    using cnf_exists[OF assms] by blast
  from Ogden_Lemma_CNF[OF P'(2) P'(1)]
  obtain n where n: "ogden_property (Lang P' S) n" ..
  have "ogden_property (Lang P S) (Suc n)"
  proof (intro ballI allI impI)
    fix z ds assume z: "z \<in> Lang P S" and m: "length ds = length z \<and> Suc n \<le> dcount ds"
    from m have lz: "length ds = length z" and dc: "Suc n \<le> dcount ds" by auto
    have "0 < length z" using dc lz count_le_length[of ds True] by linarith
    hence "z \<noteq> []" by auto
    with z P'(3) have z': "z \<in> Lang P' S" by simp
    have prem: "length ds = length z \<and> n \<le> dcount ds" using lz dc by simp
    from bspec[OF n z', rule_format, OF prem]
    obtain u v w x y du dv dw dx dy where o:
      "z = u @ v @ w @ x @ y" "ds = du @ dv @ dw @ dx @ dy"
      "length du = length u" "length dv = length v" "length dw = length w"
      "length dx = length x" "length dy = length y"
      "1 \<le> dcount (dv @ dx)" "dcount (dv @ dw @ dx) \<le> n"
      "\<forall>i. u @ v ^^ i @ w @ x ^^ i @ y \<in> Lang P' S"
      by blast
    have pumpP: "\<forall>i. u @ v ^^ i @ w @ x ^^ i @ y \<in> Lang P S"
      using o(10) by (auto simp: P'(3))
    have le: "dcount (dv @ dw @ dx) \<le> Suc n" using o(9) by linarith
    show "\<exists>u v w x y du dv dw dx dy.
            z = u @ v @ w @ x @ y \<and> ds = du @ dv @ dw @ dx @ dy \<and>
            length du = length u \<and> length dv = length v \<and> length dw = length w \<and>
              length dx = length x \<and> length dy = length y \<and>
            1 \<le> dcount (dv @ dx) \<and> dcount (dv @ dw @ dx) \<le> Suc n \<and>
            (\<forall>i. u @ v ^^ i @ w @ x ^^ i @ y \<in> Lang P S)"
      using o le pumpP by blast
  qed
  thus ?thesis by blast
qed

end
