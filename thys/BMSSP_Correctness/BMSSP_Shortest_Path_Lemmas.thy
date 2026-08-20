theory BMSSP_Shortest_Path_Lemmas
  imports BMSSP_Correctness
begin

section \<open>Shortest-Path Prefix Facts\<close>

text \<open>
  The algorithm's tree-based correctness arguments repeatedly use the fact that
  vertices appearing earlier on a shortest path have no larger true distance.
  This theory proves that fact from the finite non-negative weighted graph
  model, without assuming uniqueness of shortest paths.
\<close>

context finite_weighted_digraph
begin

lemma walk_nonempty:
  assumes "walk p"
  shows "p \<noteq> []"
  using assms by (cases p) auto

lemma walk_weight_nonneg:
  assumes "walk p"
  shows "0 \<le> walk_weight p"
  using assms
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons x ps)
  show ?case
  proof (cases ps)
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    then have edge: "(x, y) \<in> E" and tail: "walk (y # ys)"
      using Cons.prems by auto
    have wx: "0 \<le> w x y"
      using edge nonneg_weight by auto
    have tail_nonneg: "0 \<le> walk_weight (y # ys)"
      using Cons.IH tail Cons by simp
    show ?thesis
      using wx tail_nonneg Cons by simp
  qed
qed

lemma dist_nonneg:
  assumes "reachable a b"
  shows "0 \<le> dist a b"
proof -
  have "dist a b \<in> simple_walk_weights a b"
    by (rule dist_is_simple_walk_weight[OF assms])
  then obtain p where p: "simple_walk_betw a p b"
    and dist_eq: "walk_weight p = dist a b"
    unfolding simple_walk_weights_def by auto
  have "walk p"
    using p unfolding simple_walk_betw_def walk_betw_def by blast
  then have "0 \<le> walk_weight p"
    by (rule walk_weight_nonneg)
  then show ?thesis
    using dist_eq by simp
qed

lemma walk_take_Suc:
  assumes "walk p" "i < length p"
  shows "walk (take (Suc i) p)"
  using assms
proof (induction p arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x ps)
  show ?case
  proof (cases ps)
    case Nil
    then show ?thesis
      using Cons by (cases i) auto
  next
    case (Cons y ys)
    then have walk_tail: "walk (y # ys)"
      using Cons.prems by auto
    show ?thesis
    proof (cases i)
      case 0
      then show ?thesis
        using Cons.prems Cons by auto
    next
      case (Suc j)
      then have "j < length (y # ys)"
        using Cons.prems Cons by simp
      then have "walk (take (Suc j) (y # ys))"
        using Cons.IH walk_tail Cons by simp
      then show ?thesis
        using Cons.prems Cons Suc by auto
    qed
  qed
qed

lemma walk_weight_take_Suc_le:
  assumes "walk p" "i < length p"
  shows "walk_weight (take (Suc i) p) \<le> walk_weight p"
  using assms
proof (induction p arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x ps)
  show ?case
  proof (cases ps)
    case Nil
    then show ?thesis
      using Cons by (cases i) auto
  next
    case (Cons y ys)
    then have edge: "(x, y) \<in> E" and walk_tail: "walk (y # ys)"
      using Cons.prems by auto
    show ?thesis
    proof (cases i)
      case 0
      have "0 \<le> w x y"
        using edge nonneg_weight by auto
      moreover have "0 \<le> walk_weight (y # ys)"
        using walk_weight_nonneg[OF walk_tail] .
      ultimately show ?thesis
        using Cons 0 by auto
    next
      case (Suc j)
      then have j: "j < length (y # ys)"
        using Cons.prems Cons by simp
      have "walk_weight (take (Suc j) (y # ys)) \<le> walk_weight (y # ys)"
        using Cons.IH walk_tail j Cons by simp
      then show ?thesis
        using Cons Suc by auto
    qed
  qed
qed

lemma simple_walk_prefix:
  assumes p: "simple_walk_betw a p b"
    and i: "i < length p"
  shows "simple_walk_betw a (take (Suc i) p) (p ! i)"
proof -
  have nonempty: "p \<noteq> []" and hd: "hd p = a" and walk_p: "walk p" and distinct_p: "distinct p"
    using p unfolding simple_walk_betw_def walk_betw_def by auto
  have take_nonempty: "take (Suc i) p \<noteq> []"
    using i by auto
  have "hd (take (Suc i) p) = a"
    using hd i by (simp add: hd_take)
  moreover have "last (take (Suc i) p) = p ! i"
  proof -
    have len_take: "length (take (Suc i) p) = Suc i"
      using i by simp
    have "last (take (Suc i) p) =
        take (Suc i) p ! (length (take (Suc i) p) - 1)"
      using take_nonempty by (rule last_conv_nth)
    also have "\<dots> = take (Suc i) p ! i"
      using len_take by simp
    finally have "last (take (Suc i) p) = take (Suc i) p ! i" .
    then show ?thesis
      using i by simp
  qed
  moreover have "walk (take (Suc i) p)"
    using walk_take_Suc[OF walk_p i] .
  moreover have "distinct (take (Suc i) p)"
    using distinct_p by simp
  ultimately show ?thesis
    using take_nonempty unfolding simple_walk_betw_def walk_betw_def by auto
qed

lemma dist_le_simple_walk_weight:
  assumes p: "simple_walk_betw a p b"
  shows "dist a b \<le> walk_weight p"
proof -
  have mem: "walk_weight p \<in> simple_walk_weights a b"
    using p unfolding simple_walk_weights_def by blast
  have fin: "finite (simple_walk_weights a b)"
    using finite_simple_walk_weights .
  show ?thesis
    unfolding dist_def using fin mem by (rule Min_le)
qed

lemma shortest_walk_prefix_dist_le:
  assumes p: "shortest_walk a p b"
    and u: "u \<in> set p"
  shows "dist a u \<le> dist a b"
proof -
  have simple_p: "simple_walk_betw a p b"
    using p unfolding shortest_walk_def by blast
  then have walk_p: "walk p"
    unfolding simple_walk_betw_def walk_betw_def by auto
  obtain i where i: "i < length p" "p ! i = u"
    using u by (auto simp: in_set_conv_nth)
  let ?q = "take (Suc i) p"
  have simple_q: "simple_walk_betw a ?q u"
    using simple_walk_prefix[OF simple_p i(1)] i(2) by simp
  have "dist a u \<le> walk_weight ?q"
    using dist_le_simple_walk_weight[OF simple_q] .
  also have "\<dots> \<le> walk_weight p"
    using walk_weight_take_Suc_le[OF walk_p i(1)] .
  also have "\<dots> = dist a b"
    using p unfolding shortest_walk_def by simp
  finally show ?thesis .
qed

lemma through_witness_dist_le:
  assumes "through S v"
  obtains u p where "u \<in> S" "shortest_walk s p v" "u \<in> set p" "dist s u \<le> dist s v"
proof -
  obtain u p where u: "u \<in> S" "shortest_walk s p v" "u \<in> set p"
    using assms unfolding through_def by blast
  then have "dist s u \<le> dist s v"
    using shortest_walk_prefix_dist_le by blast
  then show thesis
    using that u by blast
qed

lemma walk_snoc:
  assumes walk_p: "walk p"
    and nonempty: "p \<noteq> []"
    and last_p: "last p = u"
    and edge: "(u, v) \<in> E"
  shows "walk (p @ [v])"
  using walk_p nonempty last_p edge
proof (induction p arbitrary: u)
  case Nil
  then show ?case by simp
next
  case (Cons x ps)
  show ?case
  proof (cases ps)
    case Nil
    then have xu: "x = u"
      using Cons.prems by simp
    have xv: "(x, v) \<in> E"
      using Cons.prems xu by simp
    have xV: "x \<in> V"
      using Cons.prems Nil by simp
    have vV: "v \<in> V"
      using edge edge_in_V by blast
    show ?thesis
      using xV vV xv Nil by auto
  next
    case (Cons y ys)
    have ps_walk: "walk ps"
      using Cons.prems Cons by auto
    have ps_nonempty: "ps \<noteq> []"
      using Cons by simp
    have ps_last: "last ps = u"
      using Cons.prems ps_nonempty by simp
    have tail_edge: "(u, v) \<in> E"
      using Cons.prems by simp
    have "walk (ps @ [v])"
      using Cons.IH[OF ps_walk ps_nonempty ps_last tail_edge] .
    then show ?thesis
      using Cons.prems Cons by auto
  qed
qed

lemma walk_weight_snoc:
  assumes "p \<noteq> []" "last p = u"
  shows "walk_weight (p @ [v]) = walk_weight p + w u v"
  using assms
proof (induction p arbitrary: u)
  case Nil
  then show ?case by simp
next
  case (Cons x ps)
  show ?case
  proof (cases ps)
    case Nil
    then show ?thesis
      using Cons by simp
  next
    case (Cons y ys)
    have ps_ne: "ps \<noteq> []"
      using Cons by simp
    have ps_last: "last ps = u"
      using Cons.prems ps_ne by simp
    have "walk_weight (ps @ [v]) = walk_weight ps + w u v"
      using Cons.IH[OF ps_ne ps_last] .
    then show ?thesis
      using Cons by simp
  qed
qed

lemma walk_append_tl:
  assumes walk_p: "walk p"
    and walk_q: "walk q"
    and p_ne: "p \<noteq> []"
    and q_ne: "q \<noteq> []"
    and join: "last p = hd q"
  shows "walk (p @ tl q)"
  using walk_p walk_q p_ne q_ne join
proof (induction p arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons x ps)
  show ?case
  proof (cases ps)
    case Nil
    have q_ne': "q \<noteq> []"
      using Cons.prems by blast
    have walk_q': "walk q"
      using Cons.prems by blast
    have "x = hd q"
      using Cons.prems Nil by simp
    then have "x # tl q = q"
      using q_ne' by (cases q) auto
    then show ?thesis
      using walk_q' Nil by simp
  next
    case (Cons y ys)
    have tail_walk: "walk (y # ys)"
      using Cons.prems Cons by auto
    have tail_walk_ps: "walk ps"
      using tail_walk Cons by simp
    have tail_ne: "y # ys \<noteq> []"
      by simp
    have tail_ne_ps: "ps \<noteq> []"
      using Cons by simp
    have tail_join: "last (y # ys) = hd q"
      using Cons.prems Cons by simp
    have tail_join_ps: "last ps = hd q"
      using tail_join Cons by simp
    have walk_q': "walk q"
      using Cons.prems by blast
    have q_ne': "q \<noteq> []"
      using Cons.prems by blast
    have "walk (ps @ tl q)"
      using Cons.IH[OF tail_walk_ps walk_q' tail_ne_ps q_ne' tail_join_ps] .
    then have "walk ((y # ys) @ tl q)"
      using Cons by simp
    then show ?thesis
      using Cons.prems Cons by auto
  qed
qed

lemma walk_weight_append_tl:
  assumes p_ne: "p \<noteq> []"
    and q_ne: "q \<noteq> []"
    and join: "last p = hd q"
  shows "walk_weight (p @ tl q) = walk_weight p + walk_weight q"
  using p_ne q_ne join
proof (induction p arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons x ps)
  show ?case
  proof (cases ps)
    case Nil
    have q_ne': "q \<noteq> []"
      using Cons.prems by blast
    have "x = hd q"
      using Cons.prems Nil by simp
    then have "x # tl q = q"
      using q_ne' by (cases q) auto
    then show ?thesis
      using Nil by simp
  next
    case (Cons y ys)
    have tail_ne: "y # ys \<noteq> []"
      by simp
    have tail_ne_ps: "ps \<noteq> []"
      using Cons by simp
    have tail_join: "last (y # ys) = hd q"
      using Cons.prems Cons by simp
    have tail_join_ps: "last ps = hd q"
      using tail_join Cons by simp
    have q_ne': "q \<noteq> []"
      using Cons.prems by blast
    have "walk_weight (ps @ tl q) = walk_weight ps + walk_weight q"
      using Cons.IH[OF tail_ne_ps q_ne' tail_join_ps] .
    then have "walk_weight ((y # ys) @ tl q) =
        walk_weight (y # ys) + walk_weight q"
      using Cons by simp
    then show ?thesis
      using Cons by simp
  qed
qed

lemma walk_betw_append_tl:
  assumes p: "walk_betw a p b"
    and q: "walk_betw b q c"
  shows "walk_betw a (p @ tl q) c"
proof -
  have p_ne: "p \<noteq> []" and q_ne: "q \<noteq> []"
    and hd_p: "hd p = a" and last_p: "last p = b"
    and hd_q: "hd q = b" and last_q: "last q = c"
    and walk_p: "walk p" and walk_q: "walk q"
    using p q unfolding walk_betw_def by auto
  have join: "last p = hd q"
    using last_p hd_q by simp
  have walk: "walk (p @ tl q)"
    using walk_append_tl[OF walk_p walk_q p_ne q_ne join] .
  have nonempty: "p @ tl q \<noteq> []"
    using p_ne by simp
  have hd: "hd (p @ tl q) = a"
    using hd_p p_ne by simp
  have last: "last (p @ tl q) = c"
  proof (cases "tl q = []")
    case True
    then have "q = [hd q]"
      using q_ne by (cases q) auto
    then show ?thesis
      using last_p hd_q last_q by simp
  next
    case False
    then show ?thesis
      using last_q q_ne by (cases q) auto
  qed
  show ?thesis
    using nonempty hd last walk unfolding walk_betw_def by blast
qed

lemma walk_weight_append_tl_betw:
  assumes p: "walk_betw a p b"
    and q: "walk_betw b q c"
  shows "walk_weight (p @ tl q) = walk_weight p + walk_weight q"
proof -
  have "p \<noteq> []" "q \<noteq> []" "last p = hd q"
    using p q unfolding walk_betw_def by auto
  then show ?thesis
    by (rule walk_weight_append_tl)
qed

lemma walk_suffix_append:
  assumes "walk (xs @ ys)" "ys \<noteq> []"
  shows "walk ys"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      using Cons by (cases ys) auto
  next
    case (Cons y zs)
    then have tail_walk: "walk ((y # zs) @ ys)"
      using Cons.prems by auto
    have tail_walk_ps: "walk (xs @ ys)"
      using tail_walk Cons by simp
    then show ?thesis
      using Cons.IH[OF tail_walk_ps Cons.prems(2)] by blast
  qed
qed

lemma walk_prefix_append:
  assumes "walk (xs @ ys)" "xs \<noteq> []"
  shows "walk xs"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases xs)
    case Nil
    then have "x \<in> V"
      using Cons.prems by (cases ys) auto
    then show ?thesis
      using Nil by simp
  next
    case (Cons y zs)
    then have xV: "x \<in> V" and edge: "(x, y) \<in> E" and tail_walk: "walk ((y # zs) @ ys)"
      using Cons.prems by auto
    have tail_walk_ps: "walk (xs @ ys)"
      using tail_walk Cons by simp
    have tail_ne: "xs \<noteq> []"
      using Cons by simp
    have "walk xs"
      using Cons.IH[OF tail_walk_ps tail_ne] .
    then have "walk (y # zs)"
      using Cons by simp
    then show ?thesis
      using Cons xV edge by auto
  qed
qed

lemma walk_remove_cycle:
  assumes walk_p: "walk (xs @ y # ys @ y # zs)"
  shows "walk (xs @ y # zs)"
proof -
  let ?pref = "xs @ [y]"
  let ?cycle_suffix = "y # ys @ y # zs"
  let ?suffix = "y # zs"
  have pref_walk: "walk ?pref"
    using walk_prefix_append[of ?pref "ys @ y # zs"] walk_p by simp
  have suffix_walk: "walk ?suffix"
    using walk_suffix_append[of "xs @ y # ys" ?suffix] walk_p by simp
  have pref_ne: "?pref \<noteq> []"
    by simp
  have suffix_ne: "?suffix \<noteq> []"
    by simp
  have join: "last ?pref = hd ?suffix"
    by simp
  have "walk (?pref @ tl ?suffix)"
    using walk_append_tl[OF pref_walk suffix_walk pref_ne suffix_ne join] .
  then show ?thesis
    by simp
qed

lemma walk_weight_remove_cycle_le:
  assumes walk_p: "walk (xs @ y # ys @ y # zs)"
  shows "walk_weight (xs @ y # zs) \<le> walk_weight (xs @ y # ys @ y # zs)"
proof -
  let ?pref = "xs @ [y]"
  let ?cycle = "y # ys @ [y]"
  let ?suffix = "y # zs"
  let ?cycle_suffix = "y # ys @ y # zs"
  have pref_walk: "walk ?pref"
    using walk_prefix_append[of ?pref "ys @ y # zs"] walk_p by simp
  have cycle_suffix_walk: "walk ?cycle_suffix"
    using walk_suffix_append[of xs ?cycle_suffix] walk_p by simp
  have cycle_walk: "walk ?cycle"
    using walk_prefix_append[of ?cycle zs] cycle_suffix_walk by simp
  have suffix_walk: "walk ?suffix"
    using walk_suffix_append[of "xs @ y # ys" ?suffix] walk_p by simp
  have pref_ne: "?pref \<noteq> []" and cycle_suffix_ne: "?cycle_suffix \<noteq> []"
    and cycle_ne: "?cycle \<noteq> []" and suffix_ne: "?suffix \<noteq> []"
    by simp_all
  have pref_join_cycle_suffix: "last ?pref = hd ?cycle_suffix"
    by simp
  have pref_join_suffix: "last ?pref = hd ?suffix"
    by simp
  have cycle_join_suffix: "last ?cycle = hd ?suffix"
    by simp
  have new_weight:
    "walk_weight (xs @ y # zs) = walk_weight ?pref + walk_weight ?suffix"
    using walk_weight_append_tl[OF pref_ne suffix_ne pref_join_suffix] by simp
  have original_weight:
    "walk_weight (xs @ y # ys @ y # zs) =
      walk_weight ?pref + walk_weight ?cycle_suffix"
    using walk_weight_append_tl[OF pref_ne cycle_suffix_ne pref_join_cycle_suffix] by simp
  have cycle_suffix_weight:
    "walk_weight ?cycle_suffix = walk_weight ?cycle + walk_weight ?suffix"
    using walk_weight_append_tl[OF cycle_ne suffix_ne cycle_join_suffix] by simp
  have cycle_nonneg: "0 \<le> walk_weight ?cycle"
    using walk_weight_nonneg[OF cycle_walk] .
  show ?thesis
    using new_weight original_weight cycle_suffix_weight cycle_nonneg by linarith
qed

lemma walk_betw_remove_cycle:
  assumes p: "walk_betw a (xs @ y # ys @ y # zs) b"
  shows "walk_betw a (xs @ y # zs) b"
proof -
  let ?p = "xs @ y # ys @ y # zs"
  let ?p' = "xs @ y # zs"
  have walk_p: "walk ?p"
    using p unfolding walk_betw_def by blast
  have walk_p': "walk ?p'"
    using walk_remove_cycle[OF walk_p] .
  have nonempty: "?p' \<noteq> []"
    by simp
  have hd_p: "hd ?p = a" and last_p: "last ?p = b"
    using p unfolding walk_betw_def by auto
  have hd_p': "hd ?p' = a"
    using hd_p by (cases xs) auto
  have last_p': "last ?p' = b"
    using last_p by (cases zs) auto
  show ?thesis
    using nonempty hd_p' last_p' walk_p' unfolding walk_betw_def by blast
qed

lemma walk_betw_to_simple_walk_le_exists:
  assumes p: "walk_betw a p b"
  shows "\<exists>q. simple_walk_betw a q b \<and> walk_weight q \<le> walk_weight p"
  using p
proof (induction "length p" arbitrary: p rule: less_induct)
  case less
  show ?case
  proof (cases "distinct p")
    case True
    then have "simple_walk_betw a p b"
      using less.prems unfolding simple_walk_betw_def by blast
    then show ?thesis
      by blast
  next
    case False
    then obtain xs ys zs y where decomp: "p = xs @ [y] @ ys @ [y] @ zs"
      using not_distinct_decomp by blast
    let ?p' = "xs @ y # zs"
    have p_form: "p = xs @ y # ys @ y # zs"
      using decomp by simp
    have p'_betw: "walk_betw a ?p' b"
      using walk_betw_remove_cycle[of a xs y ys zs b] less.prems p_form by simp
    have p'_shorter: "length ?p' < length p"
      using p_form by simp
    obtain q where q: "simple_walk_betw a q b" "walk_weight q \<le> walk_weight ?p'"
      using less.hyps[OF p'_shorter p'_betw] by blast
    have "walk_weight ?p' \<le> walk_weight p"
      using walk_weight_remove_cycle_le[of xs y ys zs] less.prems p_form
      unfolding walk_betw_def by simp
    then have "walk_weight q \<le> walk_weight p"
      using q(2) by linarith
    then show ?thesis
      using q(1) by blast
  qed
qed

lemma walk_betw_to_simple_walk_le:
  assumes p: "walk_betw a p b"
  obtains q where "simple_walk_betw a q b" "walk_weight q \<le> walk_weight p"
  using walk_betw_to_simple_walk_le_exists[OF p] that by blast

lemma walk_suffix_from_index:
  assumes p: "simple_walk_betw a p b"
    and i: "i < length p"
  shows "walk_betw (p ! i) (drop i p) b"
proof -
  have walk_p: "walk p" and last_p: "last p = b"
    using p unfolding simple_walk_betw_def walk_betw_def by auto
  have drop_ne: "drop i p \<noteq> []"
    using i by auto
  have hd_drop: "hd (drop i p) = p ! i"
    using i by (simp add: hd_drop_conv_nth)
  have last_drop: "last (drop i p) = b"
    using last_p i by (simp add: last_drop)
  have p_decomp: "p = take i p @ drop i p"
    by simp
  have walk_drop: "walk (drop i p)"
    using walk_suffix_append[of "take i p" "drop i p"] walk_p drop_ne p_decomp by simp
  show ?thesis
    using drop_ne hd_drop last_drop walk_drop unfolding walk_betw_def by blast
qed

lemma take_Suc_append_tl_drop:
  assumes "i < length p"
  shows "take (Suc i) p @ tl (drop i p) = p"
proof -
  have drop_i: "drop i p = p ! i # drop (Suc i) p"
    using Cons_nth_drop_Suc[OF assms] by simp
  have "take (Suc i) p @ tl (drop i p) =
      take i p @ [p ! i] @ drop (Suc i) p"
    using assms drop_i by (simp add: take_Suc_conv_app_nth)
  also have "\<dots> = take i p @ drop i p"
    using drop_i by simp
  finally show ?thesis
    by simp
qed

lemma shortest_walk_prefix_shortest:
  assumes sp: "shortest_walk a p b"
    and i: "i < length p"
  shows "shortest_walk a (take (Suc i) p) (p ! i)"
proof -
  let ?u = "p ! i"
  let ?pref = "take (Suc i) p"
  let ?suf = "drop i p"
  have simple_p: "simple_walk_betw a p b"
    using sp unfolding shortest_walk_def by blast
  have weight_p: "walk_weight p = dist a b"
    using sp unfolding shortest_walk_def by blast
  have pref_simple: "simple_walk_betw a ?pref ?u"
    using simple_walk_prefix[OF simple_p i] .
  have pref_walk_betw: "walk_betw a ?pref ?u"
    using pref_simple unfolding simple_walk_betw_def by blast
  have suf_walk_betw: "walk_betw ?u ?suf b"
    using walk_suffix_from_index[OF simple_p i] .
  have split_p: "?pref @ tl ?suf = p"
    using take_Suc_append_tl_drop[OF i] .
  have weight_split: "walk_weight p = walk_weight ?pref + walk_weight ?suf"
    using walk_weight_append_tl_betw[OF pref_walk_betw suf_walk_betw] split_p by simp
  have dist_pref_le: "dist a ?u \<le> walk_weight ?pref"
    using dist_le_simple_walk_weight[OF pref_simple] .
  have no_strict: "\<not> dist a ?u < walk_weight ?pref"
  proof
    assume strict: "dist a ?u < walk_weight ?pref"
    have reach_u: "reachable a ?u"
      using pref_simple unfolding reachable_def by blast
    obtain r where r_short: "shortest_walk a r ?u"
      using shortest_walk_exists[OF reach_u] by blast
    have r_simple: "simple_walk_betw a r ?u"
      using r_short unfolding shortest_walk_def by blast
    have r_walk_betw: "walk_betw a r ?u"
      using r_simple unfolding simple_walk_betw_def by blast
    have r_weight: "walk_weight r = dist a ?u"
      using r_short unfolding shortest_walk_def by blast
    have concat_walk: "walk_betw a (r @ tl ?suf) b"
      using walk_betw_append_tl[OF r_walk_betw suf_walk_betw] .
    have concat_weight: "walk_weight (r @ tl ?suf) = walk_weight r + walk_weight ?suf"
      using walk_weight_append_tl_betw[OF r_walk_betw suf_walk_betw] .
    obtain q where q: "simple_walk_betw a q b"
      "walk_weight q \<le> walk_weight (r @ tl ?suf)"
      using walk_betw_to_simple_walk_le[OF concat_walk] by blast
    have "walk_weight (r @ tl ?suf) < walk_weight p"
      using strict r_weight weight_split concat_weight by linarith
    then have "walk_weight q < dist a b"
      using q(2) weight_p by linarith
    moreover have "dist a b \<le> walk_weight q"
      using dist_le_simple_walk_weight[OF q(1)] .
    ultimately show False
      by linarith
  qed
  have "walk_weight ?pref = dist a ?u"
    using dist_pref_le no_strict by linarith
  then show ?thesis
    using pref_simple unfolding shortest_walk_def by blast
qed

lemma walk_nth_edge:
  assumes "walk p"
    and "Suc i < length p"
  shows "(p ! i, p ! Suc i) \<in> E"
  using assms
proof (induction p arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using Cons.prems by (cases xs) auto
  next
    case (Suc j)
    then have "Suc j < length xs"
      using Cons.prems by simp
    moreover have "walk xs"
      using Cons.prems Suc by (cases xs) auto
    ultimately have "(xs ! j, xs ! Suc j) \<in> E"
      using Cons.IH by blast
    then show ?thesis
      using Suc by simp
  qed
qed

lemma simple_walk_snoc:
  assumes p: "simple_walk_betw s p u"
    and edge: "(u, v) \<in> E"
    and fresh: "v \<notin> set p"
  shows "simple_walk_betw s (p @ [v]) v"
proof -
  have nonempty: "p \<noteq> []" and hd: "hd p = s" and last_p: "last p = u"
    and walk_p: "walk p" and distinct_p: "distinct p"
    using p unfolding simple_walk_betw_def walk_betw_def by auto
  have "walk (p @ [v])"
    using walk_snoc[OF walk_p nonempty last_p edge] .
  moreover have "p @ [v] \<noteq> []" "hd (p @ [v]) = s" "last (p @ [v]) = v" "distinct (p @ [v])"
    using nonempty hd fresh distinct_p by auto
  ultimately show ?thesis
    unfolding simple_walk_betw_def walk_betw_def by auto
qed

lemma dist_triangle_edge:
  assumes edge: "(u, v) \<in> E"
    and reach_u: "reachable s u"
  shows "reachable s v" "dist s v \<le> dist s u + w u v"
proof -
  obtain p where p: "shortest_walk s p u"
    using reach_u by (rule shortest_walk_exists)
  have simple_p: "simple_walk_betw s p u"
    using p unfolding shortest_walk_def by blast
  have weight_p: "walk_weight p = dist s u"
    using p unfolding shortest_walk_def by blast
  show reach_v: "reachable s v"
  proof (cases "v \<in> set p")
    case True
    then obtain i where i: "i < length p" "p ! i = v"
      by (auto simp: in_set_conv_nth)
    have "simple_walk_betw s (take (Suc i) p) v"
      using simple_walk_prefix[OF simple_p i(1)] i(2) by simp
    then show ?thesis
      unfolding reachable_def by blast
  next
    case False
    have "simple_walk_betw s (p @ [v]) v"
      using simple_walk_snoc[OF simple_p edge False] .
    then show ?thesis
      unfolding reachable_def by blast
  qed
  show "dist s v \<le> dist s u + w u v"
  proof (cases "v \<in> set p")
    case True
    have "dist s v \<le> dist s u"
      using shortest_walk_prefix_dist_le[OF p True] .
    moreover have "0 \<le> w u v"
      using edge nonneg_weight by auto
    ultimately show ?thesis
      by linarith
  next
    case False
    have simple_q: "simple_walk_betw s (p @ [v]) v"
      using simple_walk_snoc[OF simple_p edge False] .
    have "dist s v \<le> walk_weight (p @ [v])"
      using dist_le_simple_walk_weight[OF simple_q] .
    also have "\<dots> = dist s u + w u v"
      using simple_p weight_p unfolding simple_walk_betw_def walk_betw_def
      by (simp add: walk_weight_snoc)
    finally show ?thesis .
  qed
qed

definition sound_label where
  "sound_label d \<longleftrightarrow> (\<forall>v\<in>V. reachable s v \<longrightarrow> dist s v \<le> d v)"

definition relax_edge where
  "relax_edge d u v = (\<lambda>x. if x = v then min (d v) (d u + w u v) else d x)"

definition tight_edge_step where
  "tight_edge_step u v \<longleftrightarrow>
     (u, v) \<in> E \<and> reachable s u \<and> dist s v = dist s u + w u v"

lemma relax_edge_le:
  "relax_edge d u v x \<le> d x"
  unfolding relax_edge_def by simp

lemma shortest_walk_successively_tight:
  assumes sp: "shortest_walk s p v"
  shows "successively tight_edge_step p"
  unfolding successively_conv_nth
proof clarify
  fix i
  assume i: "Suc i < length p"
  have simple_p: "simple_walk_betw s p v"
    using sp unfolding shortest_walk_def by blast
  have walk_p: "walk p"
    using simple_p unfolding simple_walk_betw_def walk_betw_def by blast
  have edge: "(p ! i, p ! Suc i) \<in> E"
    using walk_nth_edge[OF walk_p i] .
  have pref_i: "shortest_walk s (take (Suc i) p) (p ! i)"
    using shortest_walk_prefix_shortest[OF sp] i by simp
  have pref_Suc_i: "shortest_walk s (take (Suc (Suc i)) p) (p ! Suc i)"
    using shortest_walk_prefix_shortest[OF sp i] .
  have reach_i: "reachable s (p ! i)"
    using pref_i unfolding shortest_walk_def reachable_def by blast
  have pref_i_ne: "take (Suc i) p \<noteq> []"
    using i by (cases p) auto
  have last_pref_i: "last (take (Suc i) p) = p ! i"
  proof -
    have len_take: "length (take (Suc i) p) = Suc i"
      using i by simp
    have "last (take (Suc i) p) = take (Suc i) p ! i"
      using last_conv_nth[OF pref_i_ne] len_take by simp
    then show ?thesis
      using i by simp
  qed
  have take_next:
    "take (Suc (Suc i)) p = take (Suc i) p @ [p ! Suc i]"
    using i by (simp add: take_Suc_conv_app_nth)
  have weight_step:
    "walk_weight (take (Suc (Suc i)) p) =
      walk_weight (take (Suc i) p) + w (p ! i) (p ! Suc i)"
    using walk_weight_snoc[OF pref_i_ne last_pref_i, of "p ! Suc i"] take_next by simp
  have dist_i: "walk_weight (take (Suc i) p) = dist s (p ! i)"
    using pref_i unfolding shortest_walk_def by blast
  have dist_Suc_i: "walk_weight (take (Suc (Suc i)) p) = dist s (p ! Suc i)"
    using pref_Suc_i unfolding shortest_walk_def by blast
  show "tight_edge_step (p ! i) (p ! Suc i)"
    using edge reach_i weight_step dist_i dist_Suc_i
    unfolding tight_edge_step_def by simp
qed

lemma relax_edge_sound:
  assumes sound: "sound_label d"
    and edge: "(u, v) \<in> E"
    and reach_u: "reachable s u"
  shows "sound_label (relax_edge d u v)"
proof -
  have uV: "u \<in> V"
    using edge edge_in_V by blast
  have dist_u_le: "dist s u \<le> d u"
    using sound uV reach_u unfolding sound_label_def by blast
  have triangle: "dist s v \<le> dist s u + w u v"
    using dist_triangle_edge[OF edge reach_u] by blast
  show ?thesis
    unfolding sound_label_def relax_edge_def
  proof clarify
    fix x
    assume xV: "x \<in> V" and reach_x: "reachable s x"
    show "dist s x \<le> (if x = v then min (d v) (d u + w u v) else d x)"
    proof (cases "x = v")
      case True
      have "dist s v \<le> d v"
        using sound xV reach_x True unfolding sound_label_def by blast
      moreover have "dist s v \<le> d u + w u v"
        using dist_u_le triangle by linarith
      ultimately show ?thesis
        using True by simp
    next
      case False
      then show ?thesis
      using sound xV reach_x unfolding sound_label_def by simp
    qed
  qed
qed

lemma relax_tight_edge_completes:
  assumes sound: "sound_label d"
    and complete_u: "d u = dist s u"
    and tight: "tight_edge_step u v"
  shows "sound_label (relax_edge d u v)"
    and "relax_edge d u v v = dist s v"
proof -
  have edge: "(u, v) \<in> E" and reach_u: "reachable s u"
    and dist_v: "dist s v = dist s u + w u v"
    using tight unfolding tight_edge_step_def by auto
  show "sound_label (relax_edge d u v)"
    using relax_edge_sound[OF sound edge reach_u] .
  have vV: "v \<in> V"
    using edge edge_in_V by blast
  have reach_v: "reachable s v"
    using dist_triangle_edge[OF edge reach_u] by blast
  have "dist s v \<le> d v"
    using sound vV reach_v unfolding sound_label_def by blast
  then show "relax_edge d u v v = dist s v"
    using complete_u dist_v unfolding relax_edge_def by simp
qed

fun relax_path where
  "relax_path d [] = d"
| "relax_path d [x] = d"
| "relax_path d (x # y # xs) = relax_path (relax_edge d x y) (y # xs)"

fun relax_edges where
  "relax_edges d [] = d"
| "relax_edges d ((u, v) # es) = relax_edges (relax_edge d u v) es"

fun path_edges where
  "path_edges [] = []"
| "path_edges [x] = []"
| "path_edges (x # y # xs) = (x, y) # path_edges (y # xs)"

lemma relax_edges_append:
  "relax_edges d (xs @ ys) = relax_edges (relax_edges d xs) ys"
  by (induction xs arbitrary: d) (auto split: prod.splits)

lemma relax_edges_le:
  "relax_edges d es x \<le> d x"
proof (induction es arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain u v where e: "e = (u, v)"
    by force
  have "relax_edges (relax_edge d u v) es x \<le> relax_edge d u v x"
    by (rule Cons.IH)
  also have "\<dots> \<le> d x"
    by (rule relax_edge_le)
  finally show ?case
    unfolding e by simp
qed

lemma relax_path_eq_relax_edges:
  "relax_path d p = relax_edges d (path_edges p)"
  by (induction p arbitrary: d rule: relax_path.induct) simp_all

lemma relax_edge_preserves_other:
  assumes "x \<noteq> v"
  shows "relax_edge d u v x = d x"
  using assms unfolding relax_edge_def by simp

lemma relax_edge_preserves_complete_other:
  assumes "x \<noteq> v" "d x = dist s x"
  shows "relax_edge d u v x = dist s x"
  using assms by (simp add: relax_edge_preserves_other)

lemma relax_edge_preserves_complete_sound:
  assumes sound: "sound_label d"
    and complete_x: "d x = dist s x"
    and edge: "(u, v) \<in> E"
    and reach_u: "reachable s u"
  shows "relax_edge d u v x = dist s x"
proof (cases "x = v")
  case False
  then show ?thesis
    using complete_x by (simp add: relax_edge_preserves_other)
next
  case True
  have vV: "v \<in> V"
    using edge edge_in_V by blast
  have reach_v: "reachable s v"
    using dist_triangle_edge[OF edge reach_u] by blast
  have dist_v_le_dv: "dist s v \<le> d v"
    using sound vV reach_v unfolding sound_label_def by blast
  have dist_v_le_candidate: "dist s v \<le> d u + w u v"
  proof -
    have uV: "u \<in> V"
      using edge edge_in_V by blast
    have "dist s u \<le> d u"
      using sound uV reach_u unfolding sound_label_def by blast
    moreover have "dist s v \<le> dist s u + w u v"
      using dist_triangle_edge[OF edge reach_u] by blast
    ultimately show ?thesis
      by linarith
  qed
  show ?thesis
    using True complete_x dist_v_le_dv dist_v_le_candidate unfolding relax_edge_def by simp
qed

lemma relax_edges_sound:
  assumes sound: "sound_label d"
    and edges: "\<And>u v. (u, v) \<in> set es \<Longrightarrow> (u, v) \<in> E"
    and reaches: "\<And>u v. (u, v) \<in> set es \<Longrightarrow> reachable s u"
  shows "sound_label (relax_edges d es)"
  using sound edges reaches
proof (induction es arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain u v where e: "e = (u, v)"
    by force
  have edge: "(u, v) \<in> E"
    using Cons.prems e by auto
  have reach: "reachable s u"
    using Cons.prems e by auto
  have sound1: "sound_label (relax_edge d u v)"
    using relax_edge_sound[OF Cons.prems(1) edge reach] .
  have edges_tail: "\<And>a b. (a, b) \<in> set es \<Longrightarrow> (a, b) \<in> E"
    using Cons.prems by auto
  have reaches_tail: "\<And>a b. (a, b) \<in> set es \<Longrightarrow> reachable s a"
    using Cons.prems by auto
  show ?case
    using Cons.IH[OF sound1 edges_tail reaches_tail] e by simp
qed

lemma relax_edges_preserves_complete_if_not_targeted:
  assumes complete_x: "d x = dist s x"
    and not_target: "\<And>u. (u, x) \<notin> set es"
  shows "relax_edges d es x = dist s x"
  using complete_x not_target
proof (induction es arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain u v where e: "e = (u, v)"
    by force
  have x_ne_v: "x \<noteq> v"
    using Cons.prems(2)[of u] e by auto
  have complete_after: "relax_edge d u v x = dist s x"
    using x_ne_v Cons.prems(1) unfolding relax_edge_def by simp
  have not_target_tail: "\<And>a. (a, x) \<notin> set es"
    using Cons.prems e by auto
  have "relax_edges (relax_edge d u v) es x = dist s x"
    using Cons.IH[of "relax_edge d u v"] complete_after not_target_tail by blast
  show ?case
    using \<open>relax_edges (relax_edge d u v) es x = dist s x\<close> e by simp
qed

lemma relax_edges_preserves_complete_sound:
  assumes sound: "sound_label d"
    and complete_x: "d x = dist s x"
    and edges: "\<And>u v. (u, v) \<in> set es \<Longrightarrow> (u, v) \<in> E"
    and reaches: "\<And>u v. (u, v) \<in> set es \<Longrightarrow> reachable s u"
  shows "relax_edges d es x = dist s x"
  using sound complete_x edges reaches
proof (induction es arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain u v where e: "e = (u, v)"
    by force
  have edge: "(u, v) \<in> E"
    using Cons.prems e by auto
  have reach: "reachable s u"
    using Cons.prems e by auto
  have sound1: "sound_label (relax_edge d u v)"
    using relax_edge_sound[OF Cons.prems(1) edge reach] .
  have complete_after: "relax_edge d u v x = dist s x"
    using relax_edge_preserves_complete_sound[OF Cons.prems(1) Cons.prems(2) edge reach] .
  have edges_tail: "\<And>a b. (a, b) \<in> set es \<Longrightarrow> (a, b) \<in> E"
    using Cons.prems by auto
  have reaches_tail: "\<And>a b. (a, b) \<in> set es \<Longrightarrow> reachable s a"
    using Cons.prems by auto
  have "relax_edges (relax_edge d u v) es x = dist s x"
    using Cons.IH[OF sound1 complete_after edges_tail reaches_tail] .
  then show ?case
    using e by simp
qed

lemma relax_path_tight_sound_complete:
  assumes nonempty: "p \<noteq> []"
    and sound: "sound_label d"
    and complete_hd: "d (hd p) = dist s (hd p)"
    and tight: "successively tight_edge_step p"
  shows "sound_label (relax_path d p)"
    and "relax_path d p (last p) = dist s (last p)"
proof -
  have combined: "\<And>d. p \<noteq> [] \<Longrightarrow> sound_label d \<Longrightarrow>
      d (hd p) = dist s (hd p) \<Longrightarrow> successively tight_edge_step p \<Longrightarrow>
      sound_label (relax_path d p) \<and>
      relax_path d p (last p) = dist s (last p)"
  proof (induction p)
    case Nil
    then show ?case by simp
  next
    case (Cons x ps)
    show ?case
    proof (cases "ps = []")
      case True
      then show ?thesis
        using Cons.prems by simp
    next
      case False
      then obtain y ys where ps: "ps = y # ys"
        by (cases ps) auto
      have step: "tight_edge_step x y"
        using Cons.prems ps by (simp add: successively_Cons)
      have tight_tail: "successively tight_edge_step (y # ys)"
        using Cons.prems ps by (simp add: successively_Cons)
      let ?d1 = "relax_edge d x y"
      have complete_x: "d x = dist s x"
        using Cons.prems by simp
      have sound1: "sound_label ?d1"
        using relax_tight_edge_completes(1)[OF Cons.prems(2) complete_x step] .
      have complete_y: "?d1 y = dist s y"
        using relax_tight_edge_completes(2)[OF Cons.prems(2) complete_x step] .
      have complete_hd_ps: "?d1 (hd ps) = dist s (hd ps)"
        using complete_y ps by simp
      have tight_ps: "successively tight_edge_step ps"
        using tight_tail ps by simp
      have tail: "sound_label (relax_path ?d1 ps) \<and>
          relax_path ?d1 ps (last ps) = dist s (last ps)"
        using Cons.IH[of ?d1] False sound1 complete_hd_ps tight_ps by blast
      then show ?thesis
        using ps by simp
    qed
  qed
  then show "sound_label (relax_path d p)"
    using assms by blast
  from combined show "relax_path d p (last p) = dist s (last p)"
    using assms by blast
qed

lemma relax_edges_with_tight_path_prefix_complete:
  assumes nonempty: "p \<noteq> []"
    and sound: "sound_label d"
    and complete_hd: "d (hd p) = dist s (hd p)"
    and tight: "successively tight_edge_step p"
    and es: "es = path_edges p @ extra"
    and extra_edges: "\<And>u v. (u, v) \<in> set extra \<Longrightarrow> (u, v) \<in> E"
    and extra_reaches: "\<And>u v. (u, v) \<in> set extra \<Longrightarrow> reachable s u"
  shows "sound_label (relax_edges d es)"
    and "relax_edges d es (last p) = dist s (last p)"
proof -
  let ?d1 = "relax_edges d (path_edges p)"
  have path_eq: "?d1 = relax_path d p"
    using relax_path_eq_relax_edges[of d p] by simp
  have sound1: "sound_label ?d1"
    using relax_path_tight_sound_complete(1)[OF nonempty sound complete_hd tight] path_eq by simp
  have complete_last: "?d1 (last p) = dist s (last p)"
    using relax_path_tight_sound_complete(2)[OF nonempty sound complete_hd tight] path_eq by simp
  have full: "relax_edges d es = relax_edges ?d1 extra"
    using es relax_edges_append[of d "path_edges p" extra] by simp
  show "sound_label (relax_edges d es)"
    using relax_edges_sound[OF sound1 extra_edges extra_reaches] full by simp
  show "relax_edges d es (last p) = dist s (last p)"
    using relax_edges_preserves_complete_sound[OF sound1 complete_last extra_edges extra_reaches] full by simp
qed

end

end
