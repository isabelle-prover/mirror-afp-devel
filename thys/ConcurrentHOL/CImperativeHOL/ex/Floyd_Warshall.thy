(*<*)
theory Floyd_Warshall
imports
  "../CImperativeHOL"
begin

(*>*)
section\<open> Floyd-Warshall all-pairs shortest paths \label{sec:floyd_warshall} \<close>

text\<open>

The Floyd-Warshall algorithm computes the lengths of the shortest
paths between all pairs of nodes by updating an adjacency (square)
matrix that represents the edge weights. Our goal here is to present
it at a very abstract level to exhibit the data dependencies.

Source materials:
 \<^item> \<^url>\<open>https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm\<close>
 \<^item> \<^verbatim>\<open>$AFP/Floyd_Warshall/Floyd_Warshall.thy\<close>
  \<^item> a proof by refinement yielding a thorough correctness result including negative weights but not the absence of edges
 \<^item> \<^citet>\<open>\<open>\S6.2\<close> in "Dingel:2002"\<close>
  \<^item> Overly parallelised, which is not practically useful but does reveal the data dependencies
  \<^item> the refinement is pretty much the same as the direct partial correctness proof here
  \<^item> the equivalent to \<open>fw_update\<close> is a single expression

We are not very ambitious here. This theory:
 \<^item> does not track the actual shortest paths here but it is easy to add another array to do so
 \<^item> ignores numeric concerns
 \<^item> assumes the graph is complete

A further step would be to refine the parallel program to the classic three-loop presentation.

\<close>

\<comment>\<open> body of inner loop: update the weight of path \<open>a[i, j]\<close> considering the path \<open>a[i, k] \<rightarrow> a[k, j]\<close> \<close>
definition fw_update :: "('i::Ix \<times> 'i, nat) array \<Rightarrow> 'i \<times> 'i \<Rightarrow> 'i \<Rightarrow> unit imp" where
  "fw_update = (\<lambda>a (i, j) k. do {
     ij \<leftarrow> prog.Array.nth a (i, j);
     ik \<leftarrow> prog.Array.nth a (i, k);
     kj \<leftarrow> prog.Array.nth a (k, j);
     prog.whenM (ik + kj < ij) (prog.Array.upd a (i, j) (ik + kj))
   })"

\<comment>\<open> top-level specification: we can process the nodes in an arbitrary order \<close>
definition fw_chaotic :: "('i::Ix \<times> 'i, nat) array \<Rightarrow> unit imp" where
  "fw_chaotic a =
    (let b = array.bounds a in
      prog.Array.fst_app_chaotic b (\<lambda>k. \<Parallel>(i, j)\<in>set (Ix.interval b). fw_update a (i, j) k))"

\<comment>\<open> executable version \<close>
definition fw :: "('i::Ix \<times> 'i, nat) array \<Rightarrow> unit imp" where
  "fw a =
    (let b = array.bounds a in
      prog.Array.fst_app b (\<lambda>k. \<Parallel>(i, j)\<in>set (Ix.interval b). fw_update a (i, j) k))"

lemma fw_fw_chaotic_le: \<comment>\<open> the executable program refines the specification \<close>
  shows "fw a \<le> fw_chaotic a"
unfolding fw_chaotic_def fw_def
by (strengthen ord_to_strengthen(1)[OF prog.Array.fst_app_fst_app_chaotic_le]) simp

paragraph\<open> Safety proof \<close>

type_synonym 'i matrix = "'i \<times> 'i \<Rightarrow> nat"

\<comment>\<open> The weight of the given path \<close>
fun path_weight :: "'i matrix \<Rightarrow> 'i \<times> 'i \<Rightarrow> 'i list \<Rightarrow> nat" where
  "path_weight m ij [] = m ij"
| "path_weight m ij (k # xs) = m (fst ij, k) + path_weight m (k, snd ij) xs"

\<comment>\<open> The set of acyclic paths from \<open>i\<close> to \<open>j\<close> using the nodes \<open>ks\<close> \<close>
definition paths :: "'i \<times> 'i \<Rightarrow> 'i set \<Rightarrow> 'i list set" where
  "paths ij ks = {p. set p \<subseteq> ks \<and> fst ij \<notin> set p \<and> snd ij \<notin> set p \<and> distinct p}"

\<comment>\<open> The minimum weight of a path from \<open>i\<close> to \<open>j\<close> using the nodes \<open>ks\<close>.
    See \<^verbatim>\<open>$AFP/Floyd_Warshall/Floyd_Warshall.thy\<close> for proof that these are minimal amongst all paths. \<close>
definition min_path_weight :: "'i matrix \<Rightarrow> 'i \<times> 'i \<Rightarrow> 'i set \<Rightarrow> nat" where
  "min_path_weight m ij ks = Min (path_weight m ij ` paths ij ks)"

context
  fixes a :: "('i::Ix \<times> 'i, nat) array"
  fixes m :: "'i matrix"
begin

definition fw_p_inv :: "'i \<times> 'i \<Rightarrow> 'i set \<Rightarrow> heap.t pred" where \<comment>\<open> process invariant \<close>
  "fw_p_inv ij ks = (heap.rep_inv a \<^bold>\<and> Array.get a ij \<^bold>= \<langle>min_path_weight m ij ks\<rangle>)"

definition fw_inv :: "'i set \<Rightarrow> heap.t pred" where \<comment>\<open> loop invariant \<close>
  "fw_inv ks = (\<^bold>\<forall>ij. \<langle>ij\<in>set (Array.interval a)\<rangle> \<^bold>\<longrightarrow> fw_p_inv ij ks)"

definition fw_pre :: "heap.t pred" where \<comment>\<open> overall precondition \<close>
  "fw_pre = (\<langle>Array.square a\<rangle> \<^bold>\<and> heap.rep_inv a
          \<^bold>\<and> (\<^bold>\<forall>ij. \<langle>ij\<in>set (Array.interval a)\<rangle> \<^bold>\<longrightarrow> Array.get a ij \<^bold>= \<langle>m ij\<rangle>))"

definition fw_post :: "unit \<Rightarrow> heap.t pred" where \<comment>\<open> overall postcondition \<close>
  "fw_post _ = fw_inv (set (Ix.interval (fst_bounds (array.bounds a))))"

end

setup \<open>Sign.mandatory_path "paths"\<close>

lemma I:
  assumes "set p \<subseteq> ks"
  assumes "i \<notin> set p"
  assumes "j \<notin> set p"
  assumes "distinct p"
  shows "p \<in> paths (i, j) ks"
using assms by (simp add: paths_def)

lemma Nil:
  shows "[] \<in> paths ij ks"
by (simp add: paths_def)

lemma empty:
  shows "paths ij {} = {[]}"
by (fastforce simp: paths_def)

lemma not_empty:
  shows "paths ij ks \<noteq> {}"
by (metis empty_iff paths.Nil)

lemma monotone:
  shows "mono (paths ij)"
by (rule monoI) (auto simp add: paths_def)

lemmas mono = monoD[OF paths.monotone]
lemmas strengthen[strg] = st_monotone[OF paths.monotone]

lemma finite:
  assumes "finite ks"
  shows "finite (paths ij ks)"
unfolding paths_def by (rule finite_subset[OF _ iffD1[OF finite_distinct_conv assms]]) auto

lemma unused:
  assumes "p \<in> paths ij (insert k ks)"
  assumes "k \<notin> set p"
  shows "p \<in> paths ij ks"
using assms unfolding paths_def by blast

lemma decompE:
  assumes "p \<in> paths (i, j) (insert k ks)"
  assumes "k \<in> set p"
  obtains r s
    where "p = r @ k # s"
      and "r \<in> paths (i, k) ks" and "s \<in> paths (k, j) ks"
      and "distinct (r @ s)" and "i \<notin> set (r @ k # s)" and "j \<notin> set (r @ k # s)"
using assms by (fastforce simp: paths_def dest: split_list)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "path_weight"\<close>

lemma append:
  shows "path_weight m ij (xs @ y # ys) = path_weight m (fst ij, y) xs + path_weight m (y, snd ij) ys"
by (induct xs arbitrary: ij) simp_all

setup \<open>Sign.parent_path\<close>

lemmas min_path_weightI = trans[OF min_path_weight_def Min_eqI]

setup \<open>Sign.mandatory_path "min_path_weight"\<close>

lemma fw_update:
  assumes m: "min_path_weight m (i, k) ks + min_path_weight m (k, j) ks < min_path_weight m (i, j) ks"
  assumes "finite ks"
  shows "min_path_weight m (i, j) (insert k ks)
       = min_path_weight m (i, k) ks + min_path_weight m (k, j) ks" (is "?lhs = ?rhs")
proof(rule min_path_weightI)
  from \<open>finite ks\<close> show "finite (path_weight m (i, j) ` paths (i, j) (insert k ks))"
    by (simp add: paths.finite)
next
  fix w
  assume w: "w \<in> path_weight m (i, j) ` paths (i, j) (insert k ks)"
  then obtain p where p: "w = path_weight m (i, j) p" "p \<in> paths (i, j) (insert k ks)" ..
  show "?rhs \<le> w"
  proof(cases "k \<in> set p")
    case True with m \<open>finite ks\<close> w p show ?thesis
      by (clarsimp simp: min_path_weight_def path_weight.append elim!: paths.decompE)
         (auto simp: Min_plus paths.finite paths.not_empty finite_image_set2 intro!: Min_le)
  next
    case False with m \<open>finite ks\<close> w p show ?thesis
      unfolding min_path_weight_def
      by (fastforce simp: paths.finite paths.not_empty dest: paths.unused)
  qed
next
  from \<open>finite ks\<close> obtain pik
    where pik: "pik \<in> paths (i, k) ks"
      and mpik: "Min (path_weight m (i, k) ` paths (i, k) ks) = path_weight m (i, k) pik"
    by (meson finite_set Min_in finite_imageI paths.finite image_iff image_is_empty paths.not_empty)
  from \<open>finite ks\<close> obtain pkj
    where pkj: "pkj \<in> paths (k, j) ks"
      and mpkj: "Min (path_weight m (k, j) ` paths (k, j) ks) = path_weight m (k, j) pkj"
    by (meson finite_set Min_in finite_imageI paths.finite image_iff image_is_empty paths.not_empty)
  let ?p = "pik @ k # pkj"
  have "?p \<in> paths (i, j) (insert k ks)"
  proof(rule paths.I)
    from pik pkj
    show "set ?p \<subseteq> insert k ks" by (auto simp: paths_def)
    show "i \<notin> set ?p"
    proof(rule notI)
      assume "i \<in> set ?p"
      with m pik have "i \<in> set pkj" by (fastforce simp: paths_def) (* m implies i \<noteq> k *)
      then obtain p' zs where *: "pkj = zs @ i # p'" by (meson split_list)
      moreover from pkj * have "p' \<in> paths (i, j) ks" by (simp add: paths_def)
      moreover note m \<open>finite ks\<close> mpkj
      ultimately show False by (simp add: paths.finite leD min_path_weight_def path_weight.append trans_le_add2)
    qed
    show "j \<notin> set ?p"
    proof(rule notI)
      assume "j \<in> set ?p"
      with m pkj have "j \<in> set pik" by (fastforce simp: paths_def) (* m implies j \<noteq> k *)
      then obtain p' zs where *: "pik = p' @ j # zs" by (meson split_list)
      moreover from pik * have "p' \<in> paths (i, j) ks" by (simp add: paths_def)
      moreover note m \<open>finite ks\<close> mpik
      ultimately show False
        by (fastforce simp: min_path_weight_def path_weight.append paths.finite paths.not_empty)
    qed
    show "distinct ?p"
    proof(rule ccontr)
      let ?p1 = "takeWhile (\<lambda>x. x \<notin> set pkj) pik"
      let ?l = "hd (drop (length ?p1) pik)"
      let ?p2 = "tl (dropWhile (\<lambda>x. x \<noteq> ?l) pkj)"
      let ?p' = "?p1 @ ?l # ?p2"
      assume "\<not>distinct (pik @ k # pkj)"
      from pik pkj \<open>\<not>distinct (pik @ k # pkj)\<close> have "strict_prefix ?p1 pik"
        by (auto simp: paths_def strict_prefix_def takeWhile_is_prefix)
      from pik pkj \<open>\<not>distinct (pik @ k # pkj)\<close> \<open>strict_prefix ?p1 pik\<close> have "strict_suffix ?p2 pkj"
        by (fastforce simp: dropWhile_eq_drop tl_drop
                     intro: drop_strict_suffix[OF strict_suffix_tl]
                      dest: prefix_length_less nth_length_takeWhile)
      from \<open>strict_prefix ?p1 pik\<close> have "?l \<in> set pkj"
        by (fastforce simp: hd_drop_conv_nth dest: prefix_length_less nth_length_takeWhile)
      have "?p' \<in> paths (i, j) ks"
      proof(rule paths.I)
        from pik pkj \<open>strict_prefix ?p1 pik\<close> \<open>strict_suffix ?p2 pkj\<close> \<open>?l \<in> set pkj\<close> show "set ?p' \<subseteq> ks"
          by (force dest: set_takeWhileD strict_suffix_set_subset simp: paths_def)
        from \<open>i \<notin> set ?p\<close> \<open>strict_suffix ?p2 pkj\<close> \<open>?l \<in> set pkj\<close> show "i \<notin> set ?p'"
          by (auto dest: set_takeWhileD strict_suffix_set_subset)
        from \<open>j \<notin> set ?p\<close> \<open>strict_suffix ?p2 pkj\<close> \<open>?l \<in> set pkj\<close> show "j \<notin> set ?p'"
          by (auto dest: set_takeWhileD strict_suffix_set_subset)
        from pik pkj \<open>strict_suffix ?p2 pkj\<close> \<open>?l \<in> set pkj\<close> show "distinct ?p'"
          by (auto simp: paths_def distinct_tl dest!: set_takeWhileD strict_suffix_set_subset
              simp flip: arg_cong[where f=set, OF takeWhile_neq_rev, simplified])
      qed
      have "path_weight m (i, j) ?p' \<le> path_weight m (i, k) pik + path_weight m (k, j) pkj"
        unfolding path_weight.append
      proof(induct rule: add_le_mono[case_names l r])
        case l from \<open>strict_prefix ?p1 pik\<close> show ?case
          by (metis append.right_neutral append_take_drop_id fst_conv linorder_le_less_linear
                    list.collapse not_add_less1 path_weight.append prefix_order.less_le takeWhile_eq_take)
      next
        case r from \<open>?l \<in> set pkj\<close> show ?case
          by (smt (verit) append.right_neutral hd_dropWhile le_add2 list.collapse path_weight.append
                          set_takeWhileD snd_conv takeWhile_dropWhile_id)
      qed
      with m \<open>finite ks\<close> mpik mpkj \<open>?p' \<in> paths (i, j) ks\<close> show False
        by (fastforce simp: min_path_weight_def paths.finite paths.not_empty)
    qed
  qed
  with m mpik mpkj
  show "?rhs \<in> path_weight m (i, j) ` paths (i, j) (insert k ks)"
    by (force simp: min_path_weight_def path_weight.append)
qed

lemma return:
  assumes m: "\<not>(min_path_weight m (i, k) ks + min_path_weight m (k, j) ks < min_path_weight m (i, j) ks)"
  assumes "finite ks"
  shows "min_path_weight m (i, j) (insert k ks) = min_path_weight m (i, j) ks"
unfolding min_path_weight_def
proof(rule Min_eqI)
  from \<open>finite ks\<close> show "finite (path_weight m (i, j) ` paths (i, j) (insert k ks))"
    by (simp add: paths.finite)
next
  fix w
  assume w: "w \<in> path_weight m (i, j) ` paths (i, j) (insert k ks)"
  then obtain p where p: "w = path_weight m (i, j) p" "p \<in> paths (i, j) (insert k ks)" ..
  with m \<open>finite ks\<close> show "Min (path_weight m (i, j) ` paths (i, j) ks) \<le> w"
  proof(cases "k \<in> set p")
    case True with m \<open>finite ks\<close> w p show ?thesis
      by (auto simp: not_less min_path_weight_def path_weight.append paths.finite
              intro: order.trans[OF add_mono[OF Min_le Min_le]]
              elim!: order.trans paths.decompE)
  next
    case False with m \<open>finite ks\<close> w p show ?thesis
      by (meson Min_le finite_imageI paths.finite image_eqI paths.unused)
  qed
next
  from \<open>finite ks\<close>
  show "Min (path_weight m (i, j) ` paths (i, j) ks) \<in> path_weight m (i, j) ` paths (i, j) (insert k ks)"
    by (fastforce simp: paths.finite paths.not_empty intro: subsetD[OF _ Min_in] subsetD[OF paths.mono])
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "stable"\<close>

lemma Id_on_fw_inv:
  shows "stable heap.Id\<^bsub>{a}\<^esub> (fw_inv a m ys)"
by (auto simp: fw_inv_def fw_p_inv_def intro!: stable.intro stable.impliesI)

lemma Id_on_fw_p_inv:
  shows "stable heap.Id\<^bsub>{a}\<^esub> (fw_p_inv a m ij ks)"
by (auto simp: fw_p_inv_def intro: stable.intro)

lemma modifies_fw_p_inv:
  assumes "ij \<in> set (Array.interval a) - is"
  shows "stable Array.modifies\<^bsub>a, is\<^esub> (fw_p_inv a m ij ks)"
using assms by (auto simp: fw_p_inv_def intro: stable.intro)

setup \<open>Sign.parent_path\<close>

lemma fw_p_inv_cong:
  assumes "a = a'"
  assumes "m = m'"
  assumes "ij = ij'"
  assumes "ks = ks'"
  assumes "s (heap.addr_of a) = s' (heap.addr_of a')"
  shows "fw_p_inv a m ij ks s = fw_p_inv a' m' ij' ks' s'"
using assms by (simp add: fw_p_inv_def cong: heap.obj_at.cong Array.get.weak_cong)

lemma fw_p_invD:
  assumes "fw_p_inv a m ij ks s"
  shows "heap.rep_inv a s"
    and "Array.get a ij s = min_path_weight m ij ks"
using assms unfolding fw_p_inv_def by blast+

lemma fw_p_inv_fw_update:
  assumes "finite ks"
  assumes "ij \<in> set (Array.interval a)"
  assumes "fw_p_inv a m ij ks s"
  assumes "min_path_weight m (fst ij, k) ks + min_path_weight m (k, snd ij) ks < min_path_weight m ij ks"
  shows "fw_p_inv a m ij (insert k ks) (Array.set a ij (min_path_weight m (fst ij, k) ks + min_path_weight m (k, snd ij) ks) s)"
using assms by (cases ij) (simp add: fw_p_inv_def Array.simps' min_path_weight.fw_update)

lemma fw_p_inv_return:
  assumes "finite ks"
  assumes "fw_p_inv a m ij ks s"
  assumes "\<not>(min_path_weight m (fst ij, k) ks + min_path_weight m (k, snd ij) ks < min_path_weight m ij ks)"
  shows "fw_p_inv a m ij (insert k ks) s"
using assms by (cases ij) (simp add: fw_p_inv_def min_path_weight.return)

setup \<open>Sign.mandatory_path "ag"\<close>

text\<open>

\<^citet>\<open>\<open>p109\<close> in "Dingel:2000"\<close> key intuition: when processing index \<open>k\<close>, neither \<open>a[i, k]\<close> and \<open>a[k, j]\<close> change.
 \<^item> his argument is bogus: it is enough to observe that shortest paths never get shorter by adding edges
 \<^item> he unnecessarily assumes that \<open>\<delta>(i, i) = 0\<close> for all \<open>i\<close>

\<close>

lemma fw_update:
  assumes "insert k ks \<subseteq> set (Ix.interval (fst_bounds (array.bounds a)))"
  assumes "Array.square a"
  assumes ij: "ij \<in> set (Array.interval a)"
  defines "\<And>ij. G ij \<equiv> Array.modifies\<^bsub>a, {ij |_::unit. k \<notin> {fst ij, snd ij}}\<^esub>"
  defines "A \<equiv> heap.Id\<^bsub>{a}\<^esub> \<union> \<Union> (G ` (set (Array.interval a) - {ij}))"
  shows "prog.p2s (fw_update a ij k)
          \<le> \<lbrace>fw_p_inv a m ij ks \<^bold>\<and> fw_p_inv a m (fst ij, k) ks \<^bold>\<and> fw_p_inv a m (k, snd ij) ks\<rbrace>, A
           \<turnstile> G ij, \<lbrace>\<lambda>_. fw_p_inv a m ij (insert k ks)\<rbrace>"
proof -
  from assms(1) have "finite ks"
    using finite_subset by auto
  from assms(1-3) have ijk: "(fst ij, k) \<in> set (Array.interval a)" "(k, snd ij) \<in> set (Array.interval a)"
    by (auto simp: Ix.square_def interval_prod_def)
  show ?thesis
apply (simp add: fw_update_def split_def)
apply (rule ag.pre_pre)
 apply (rule ag.prog.bind)+
    apply (rule ag.prog.if)
    apply (rename_tac v\<^sub>i\<^sub>j v\<^sub>i\<^sub>k v\<^sub>k\<^sub>j)
    apply (subst prog.Array.upd_def)
    apply (rule_tac P="\<lambda>s. fw_p_inv a m ij ks s \<and> fw_p_inv a m (fst ij, k) ks s \<and> fw_p_inv a m (k, snd ij) ks s
                         \<and> v\<^sub>i\<^sub>j = Array.get a ij s \<and> v\<^sub>i\<^sub>k = Array.get a (fst ij, k) s \<and> v\<^sub>k\<^sub>j = Array.get a (k, snd ij) s"
                in ag.prog.action)
        apply (clarsimp simp: \<open>finite ks\<close> fw_p_invD(2) fw_p_inv_fw_update ij; fail)
       using ij apply (fastforce simp: G_def intro: Array.modifies.Array_set dest: fw_p_invD(1))
      using ij ijk apply (fastforce simp: A_def G_def intro: stable.intro stable.Id_on_fw_p_inv stable.modifies_fw_p_inv)
     using ij ijk apply (fastforce simp: A_def G_def intro: stable.intro stable.Id_on_fw_p_inv stable.modifies_fw_p_inv)
    apply (rename_tac v\<^sub>i\<^sub>j v\<^sub>i\<^sub>k v\<^sub>k\<^sub>j)
    apply (rule_tac Q="\<lambda>_ s. v\<^sub>i\<^sub>j = Array.get a ij s \<and> v\<^sub>i\<^sub>k = Array.get a (fst ij, k) s \<and> v\<^sub>k\<^sub>j = Array.get a (k, snd ij) s"
                 in ag.augment_post)
    apply (rule ag.prog.return)
    using ij ijk apply (fastforce simp: A_def G_def intro: stable.intro stable.Id_on_fw_p_inv stable.modifies_fw_p_inv)
   apply (rename_tac v\<^sub>i\<^sub>j v\<^sub>i\<^sub>k)
   apply (rule_tac Q="\<lambda>v s. fw_p_inv a m ij ks s \<and> fw_p_inv a m (fst ij, k) ks s \<and> fw_p_inv a m (k, snd ij) ks s
                          \<and> v\<^sub>i\<^sub>j = Array.get a ij s \<and> v\<^sub>i\<^sub>k = Array.get a (fst ij, k) s \<and> v = Array.get a (k, snd ij) s"
                in ag.post_imp)
    apply (force simp: \<open>finite ks\<close> fw_p_invD(2) fw_p_inv_return)
   apply (subst prog.Array.nth_def)
   apply (rule ag.prog.action)
      apply (clarsimp split del: if_split; assumption)
     apply fast
    using ij ijk apply (fastforce simp: A_def G_def intro: stable.intro stable.Id_on_fw_p_inv stable.modifies_fw_p_inv)
   using ij ijk apply (fastforce simp: A_def G_def intro: stable.intro stable.Id_on_fw_p_inv stable.modifies_fw_p_inv)
  apply (subst prog.Array.nth_def)
  apply (rule ag.prog.action)
     apply (clarsimp; assumption)
    apply fast
   using ij ijk apply (fastforce simp: A_def G_def intro: stable.intro stable.Id_on_fw_p_inv stable.modifies_fw_p_inv)
  using ij ijk apply (fastforce simp: A_def G_def intro: stable.intro stable.Id_on_fw_p_inv stable.modifies_fw_p_inv)
 apply (subst prog.Array.nth_def)
 apply (rule ag.prog.action)
    apply (clarsimp; assumption)
   apply fast
  using ij ijk apply (fastforce simp: A_def G_def intro: stable.intro stable.Id_on_fw_p_inv stable.modifies_fw_p_inv)
 using ij ijk apply (fastforce simp: A_def G_def intro: stable.intro stable.Id_on_fw_p_inv stable.modifies_fw_p_inv)
apply blast
done
qed

lemma fw_chaotic:
  fixes a :: "('i::Ix \<times> 'i, nat) array"
  fixes m :: "'i matrix"
  shows "prog.p2s (fw_chaotic a) \<le> \<lbrace>fw_pre a m\<rbrace>, heap.Id\<^bsub>{a}\<^esub> \<turnstile> heap.modifies\<^bsub>{a}\<^esub>, \<lbrace>fw_post a m\<rbrace>"
unfolding fw_chaotic_def fw_pre_def
apply (simp add: prog.p2s.simps Let_def split_def)
apply (rule ag.gen_asm)
apply (rule ag.pre_pre_post)
  apply (rule ag.prog.fst_app_chaotic[where P="fw_inv a m"])
   apply (rule ag.pre)
       apply (rule ag.prog.Parallel)
       apply (rule ag.fw_update[where m=m])
         apply (simp; fail)
        apply (simp; fail)
       apply (simp; fail)
      apply (fastforce simp: fw_inv_def split_def Ix.prod.interval_conv Ix.square.conv)
     apply blast
    using Array.modifies.heap_modifies_le apply blast
   apply (simp add: fw_inv_def; fail)
  apply (simp add: stable.Id_on_fw_inv; fail)
 apply (fastforce simp: fw_pre_def fw_inv_def fw_p_inv_def min_path_weight_def paths.empty)
apply (fastforce simp: fw_post_def split_def stable.Id_on_fw_inv)
done

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
