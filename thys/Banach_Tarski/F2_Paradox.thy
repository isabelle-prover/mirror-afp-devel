(*  Title:       F2_Paradox.thy
    Author:      Arthur F. Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz, 2026

    The free group F\<^sub>2 admits a paradoxical decomposition under its
    own action on itself by left multiplication. This is the algebraic
    core of the Banach-Tarski paradox.
*)

theory F2_Paradox
  imports
    Free_Group_F2
    Paradoxical_Decomposition
begin

section \<open>The action of \<open>F\<^sub>2\<close> on itself by left multiplication\<close>

text \<open>
  We interpret @{locale group_action} with carrier
  @{term "carrier F2"} and the action being left multiplication.
\<close>

lemma F2_one_in_carrier [simp]: "[] \<in> carrier F2"
  by (metis F2_is_group F2_one group.is_monoid monoid.one_closed)

interpretation F2_act:
  group_action "carrier F2" "[]" "(\<otimes>\<^bsub>F2\<^esub>)" "(\<otimes>\<^bsub>F2\<^esub>)" "carrier F2"
proof unfold_locales
  show "[] \<in> carrier F2" by simp
next
  fix g h assume "g \<in> carrier F2" "h \<in> carrier F2"
  thus "g \<otimes>\<^bsub>F2\<^esub> h \<in> carrier F2"
    by (meson F2_is_group group.is_monoid monoid.m_closed)
next
  fix x assume xin: "x \<in> carrier F2"
  have "[] \<otimes>\<^bsub>F2\<^esub> x = \<one>\<^bsub>F2\<^esub> \<otimes>\<^bsub>F2\<^esub> x" by simp
  also have "\<dots> = x" using xin F2_is_group group.is_monoid monoid.l_one by metis
  finally show "[] \<otimes>\<^bsub>F2\<^esub> x = x" .
next
  fix g h x
  assume "g \<in> carrier F2" "h \<in> carrier F2" "x \<in> carrier F2"
  thus "(g \<otimes>\<^bsub>F2\<^esub> h) \<otimes>\<^bsub>F2\<^esub> x = g \<otimes>\<^bsub>F2\<^esub> (h \<otimes>\<^bsub>F2\<^esub> x)"
    by (meson F2_is_group group.is_monoid monoid.m_assoc)
qed


section \<open>Behaviour of left multiplication by \<open>a\<close>\<close>

text \<open>
  When we left-multiply a word that begins with \<open>a\<^sup>-\<^sup>1\<close> by
  \<open>a\<close>, the leading pair cancels, and the result is exactly the
  tail of the original word.
\<close>

lemma a_mult_starts_with_aI:
  assumes "w \<in> S_aI"
  shows "a_elt \<otimes>\<^bsub>F2\<^esub> w = tl w"
proof -
  from assms have w_in: "w \<in> carrier F2"
    and w_ne: "w \<noteq> []"
    and w_hd: "hd w = (True, A)"
    by (auto simp: starts_with_def)
  from w_ne w_hd obtain u where w_eq: "w = (True, A) # u"
    by (cases w) auto
  from w_in have w_canc: "canceled w" by auto
  with w_eq have u_canc: "canceled u" using cons_canceled by metis

  have can: "canceling (False, A) (True, A)"
    by (simp add: canceling_def)
  have prep: "a_elt @ w = [(False, A), (True, A)] @ u"
    using w_eq by simp
  have step: "cancels_to_1_at 0 ([(False, A), (True, A)] @ u) u"
    using can by (auto simp: cancels_to_1_at_def cancel_at_def)
  hence "cancels_to_1 (a_elt @ w) u" using prep
    by (auto simp: cancels_to_1_def)
  hence "cancels_to (a_elt @ w) u"
    by (auto simp: cancels_to_def)
  hence norm: "normalize (a_elt @ w) = u"
    using u_canc by (rule normalize_discover[rotated])
  show ?thesis using norm w_eq
    by (simp add: F2_mult)
qed

lemma b_mult_starts_with_bI:
  assumes "w \<in> S_bI"
  shows "b_elt \<otimes>\<^bsub>F2\<^esub> w = tl w"
proof -
  from assms have w_in: "w \<in> carrier F2"
    and w_ne: "w \<noteq> []"
    and w_hd: "hd w = (True, B)"
    by (auto simp: starts_with_def)
  from w_ne w_hd obtain u where w_eq: "w = (True, B) # u"
    by (cases w) auto
  from w_in have w_canc: "canceled w" by auto
  with w_eq have u_canc: "canceled u" using cons_canceled by metis

  have can: "canceling (False, B) (True, B)"
    by (simp add: canceling_def)
  have prep: "b_elt @ w = [(False, B), (True, B)] @ u"
    using w_eq by simp
  have step: "cancels_to_1_at 0 ([(False, B), (True, B)] @ u) u"
    using can by (auto simp: cancels_to_1_at_def cancel_at_def)
  hence "cancels_to_1 (b_elt @ w) u" using prep
    by (auto simp: cancels_to_1_def)
  hence "cancels_to (b_elt @ w) u"
    by (auto simp: cancels_to_def)
  hence norm: "normalize (b_elt @ w) = u"
    using u_canc by (rule normalize_discover[rotated])
  show ?thesis using norm w_eq
    by (simp add: F2_mult)
qed


section \<open>Image computations\<close>

text \<open>
  Translating \<open>S\<^sub>a\<^sup>-\<^sup>1\<close> on the left by \<open>a\<close> yields
  exactly the carrier of \<open>F\<^sub>2\<close> minus \<open>S\<^sub>a\<close>.
\<close>

lemma image_a_S_aI:
  shows "(\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI = carrier F2 - S_a"
proof
  show "(\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI \<subseteq> carrier F2 - S_a"
  proof
    fix v assume "v \<in> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI"
    then obtain w where w: "w \<in> S_aI" and v_eq: "v = a_elt \<otimes>\<^bsub>F2\<^esub> w" by auto
    from w have w_in: "w \<in> carrier F2" and w_ne: "w \<noteq> []"
      and w_hd: "hd w = (True, A)"
      by (auto simp: starts_with_def)
    from w_ne w_hd obtain u where w_eq: "w = (True, A) # u"
      by (cases w) auto
    from a_mult_starts_with_aI[OF w] have v_tl: "v = tl w" using v_eq by simp
    hence v_u: "v = u" using w_eq by simp
    from w_in have "canceled w" by auto
    with w_eq have u_canc: "canceled u" using cons_canceled by metis
    have v_canc: "canceled v" using v_u u_canc by simp
    hence v_in: "v \<in> carrier F2" by (rule canceled_in_F2)
    have not_starts_a: "v \<notin> S_a"
    proof (cases u)
      case Nil with v_u show ?thesis by (auto simp: starts_with_def)
    next
      case (Cons p ps)
      have w_split: "w = [(True, A), p] @ ps" using w_eq Cons by simp
      have ncan: "\<not> canceling (True, A) p"
      proof
        assume can_pair: "canceling (True, A) p"
        have "cancels_to_1_at 0 w ps"
          using w_split can_pair
          by (auto simp: cancels_to_1_at_def cancel_at_def)
        hence "cancels_to_1 w ps"
          by (auto simp: cancels_to_1_def)
        hence "\<not> canceled w"
          by (auto simp: canceled_def)
        with \<open>canceled w\<close> show False by contradiction
      qed
      hence "p \<noteq> (False, A)"
        by (auto simp: canceling_def)
      hence hd_neq: "hd v \<noteq> (False, A)"
        using Cons v_u by simp
      thus ?thesis using v_in by (auto simp: starts_with_def)
    qed
    show "v \<in> carrier F2 - S_a" using v_in not_starts_a by simp
  qed
next
  show "carrier F2 - S_a \<subseteq> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI"
  proof
    fix v assume v: "v \<in> carrier F2 - S_a"
    hence v_in: "v \<in> carrier F2" and v_not_a: "v \<notin> S_a" by auto
    let ?w = "(True, A) # v"
    have v_canc: "canceled v" using v_in by auto
    have ncan: "v = [] \<or> \<not> canceling (True, A) (hd v)"
    proof (cases v)
      case Nil thus ?thesis by simp
    next
      case (Cons p ps)
      from v_not_a Cons v_in have "p \<noteq> (False, A)"
        by (auto simp: starts_with_def)
      hence "\<not> canceling (True, A) p"
        by (cases p) (auto simp: canceling_def)
      with Cons show ?thesis by simp
    qed
    have w_canc: "canceled ?w"
    proof (rule ccontr)
      assume "\<not> canceled ?w"
      then obtain w' where "cancels_to_1 ?w w'"
        by (auto simp: canceled_def)
      then obtain xs1 x1 x2 xs2
        where decomp: "?w = xs1 @ x1 # x2 # xs2"
        and can12: "canceling x1 x2"
        by (rule cancels_to_1_unfold)
      show False
      proof (cases xs1)
        case Nil
        with decomp have x1_eq: "x1 = (True, A)" by simp
        from decomp Nil have v_eq: "v = x2 # xs2" by simp
        from v_eq x1_eq can12 ncan show False by simp
      next
        case (Cons y ys)
        with decomp have v_decomp: "v = ys @ x1 # x2 # xs2" by simp
        with can12 have "\<not> canceled v"
          unfolding canceled_def
          by (auto intro: cancels_to_1_fold)
        with v_canc show False by contradiction
      qed
    qed
    hence w_in: "?w \<in> carrier F2" by auto
    have w_starts: "?w \<in> S_aI" using w_in by (auto simp: starts_with_def)
    have v_eq: "v = a_elt \<otimes>\<^bsub>F2\<^esub> ?w"
      using a_mult_starts_with_aI[OF w_starts] by simp
    show "v \<in> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI" using v_eq w_starts by auto
  qed
qed

lemma image_b_S_bI:
  shows "(\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI = carrier F2 - S_b"
proof
  show "(\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI \<subseteq> carrier F2 - S_b"
  proof
    fix v assume "v \<in> (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI"
    then obtain w where w: "w \<in> S_bI" and v_eq: "v = b_elt \<otimes>\<^bsub>F2\<^esub> w" by auto
    from w have w_in: "w \<in> carrier F2" and w_ne: "w \<noteq> []"
      and w_hd: "hd w = (True, B)"
      by (auto simp: starts_with_def)
    from w_ne w_hd obtain u where w_eq: "w = (True, B) # u"
      by (cases w) auto
    from b_mult_starts_with_bI[OF w] have v_tl: "v = tl w" using v_eq by simp
    hence v_u: "v = u" using w_eq by simp
    from w_in have "canceled w" by auto
    with w_eq have u_canc: "canceled u" using cons_canceled by metis
    have v_canc: "canceled v" using v_u u_canc by simp
    hence v_in: "v \<in> carrier F2" by (rule canceled_in_F2)
    have not_starts_b: "v \<notin> S_b"
    proof (cases u)
      case Nil with v_u show ?thesis by (auto simp: starts_with_def)
    next
      case (Cons p ps)
      have w_split: "w = [(True, B), p] @ ps" using w_eq Cons by simp
      have ncan: "\<not> canceling (True, B) p"
      proof
        assume can_pair: "canceling (True, B) p"
        have "cancels_to_1_at 0 w ps"
          using w_split can_pair
          by (auto simp: cancels_to_1_at_def cancel_at_def)
        hence "cancels_to_1 w ps"
          by (auto simp: cancels_to_1_def)
        hence "\<not> canceled w"
          by (auto simp: canceled_def)
        with \<open>canceled w\<close> show False by contradiction
      qed
      hence "p \<noteq> (False, B)"
        by (auto simp: canceling_def)
      hence hd_neq: "hd v \<noteq> (False, B)"
        using Cons v_u by simp
      thus ?thesis using v_in by (auto simp: starts_with_def)
    qed
    show "v \<in> carrier F2 - S_b" using v_in not_starts_b by simp
  qed
next
  show "carrier F2 - S_b \<subseteq> (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI"
  proof
    fix v assume v: "v \<in> carrier F2 - S_b"
    hence v_in: "v \<in> carrier F2" and v_not_b: "v \<notin> S_b" by auto
    let ?w = "(True, B) # v"
    have v_canc: "canceled v" using v_in by auto
    have ncan: "v = [] \<or> \<not> canceling (True, B) (hd v)"
    proof (cases v)
      case Nil thus ?thesis by simp
    next
      case (Cons p ps)
      from v_not_b Cons v_in have "p \<noteq> (False, B)"
        by (auto simp: starts_with_def)
      hence "\<not> canceling (True, B) p"
        by (cases p) (auto simp: canceling_def)
      with Cons show ?thesis by simp
    qed
    have w_canc: "canceled ?w"
    proof (rule ccontr)
      assume "\<not> canceled ?w"
      then obtain w' where "cancels_to_1 ?w w'"
        by (auto simp: canceled_def)
      then obtain xs1 x1 x2 xs2
        where decomp: "?w = xs1 @ x1 # x2 # xs2"
        and can12: "canceling x1 x2"
        by (rule cancels_to_1_unfold)
      show False
      proof (cases xs1)
        case Nil
        with decomp have x1_eq: "x1 = (True, B)" by simp
        from decomp Nil have v_eq: "v = x2 # xs2" by simp
        from v_eq x1_eq can12 ncan show False by simp
      next
        case (Cons y ys)
        with decomp have v_decomp: "v = ys @ x1 # x2 # xs2" by simp
        with can12 have "\<not> canceled v"
          unfolding canceled_def
          by (auto intro: cancels_to_1_fold)
        with v_canc show False by contradiction
      qed
    qed
    hence w_in: "?w \<in> carrier F2" by auto
    have w_starts: "?w \<in> S_bI" using w_in by (auto simp: starts_with_def)
    have v_eq: "v = b_elt \<otimes>\<^bsub>F2\<^esub> ?w"
      using b_mult_starts_with_bI[OF w_starts] by simp
    show "v \<in> (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI" using v_eq w_starts by auto
  qed
qed


section \<open>The paradoxical decomposition of \<open>F\<^sub>2\<close>\<close>

text \<open>
  Putting everything together: \<open>S\<^sub>a\<close> together with the
  \<open>a\<close>-translate of \<open>S\<^sub>a\<^sup>-\<^sup>1\<close> covers
  \<open>F\<^sub>2\<close> (disjointly), and symmetrically for \<open>b\<close>.
  Hence \<open>F\<^sub>2\<close> is paradoxical.
\<close>

lemma S_a_un_image_a_S_aI: "S_a \<union> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI = carrier F2"
  using image_a_S_aI starts_with_subset by blast

lemma S_b_un_image_b_S_bI: "S_b \<union> (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI = carrier F2"
  using image_b_S_bI starts_with_subset by blast

lemma S_a_disj_image_a_S_aI: "S_a \<inter> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI = {}"
  using image_a_S_aI by blast

lemma S_b_disj_image_b_S_bI: "S_b \<inter> (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI = {}"
  using image_b_S_bI by blast

definition aI_ray :: "(bool \<times> gen2) list set" where
  "aI_ray = {replicate n (True, A) | n. True}"

lemma canceled_replicate_aI: "canceled (replicate n (True, A))"
  unfolding canceled_def
proof
  assume "Domainp cancels_to_1 (replicate n (True, A))"
  then obtain w where "cancels_to_1 (replicate n (True, A)) w"
    by auto
  then obtain i where i: "Suc i < length (replicate n (True, A))"
    and "canceling (replicate n (True, A) ! i) (replicate n (True, A) ! Suc i)"
    by (auto simp: cancels_to_1_def cancels_to_1_at_def)
  hence "canceling (True, A) (True, A)"
    by simp
  thus False
    by (simp add: canceling_def)
qed

lemma aI_ray_subset_carrier: "aI_ray \<subseteq> carrier F2"
  unfolding aI_ray_def
  by (auto intro: canceled_in_F2 canceled_replicate_aI)

lemma aI_ray_cases:
  assumes "w \<in> aI_ray"
  shows "w = [] \<or> w \<in> S_aI"
proof -
  from assms obtain n where w: "w = replicate n (True, A)"
    unfolding aI_ray_def by blast
  show ?thesis
  proof (cases n)
    case 0
    with w show ?thesis by simp
  next
    case (Suc m)
    hence "w \<noteq> []" "hd w = (True, A)" "w \<in> carrier F2"
      using w aI_ray_subset_carrier assms by auto
    thus ?thesis
      by (auto simp: starts_with_def)
  qed
qed

lemma a_mult_aI_ray_pos:
  "(\<otimes>\<^bsub>F2\<^esub>) a_elt ` (aI_ray - {[]}) = aI_ray"
proof
  show "(\<otimes>\<^bsub>F2\<^esub>) a_elt ` (aI_ray - {[]}) \<subseteq> aI_ray"
  proof
    fix y
    assume "y \<in> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` (aI_ray - {[]})"
    then obtain w where w_ray: "w \<in> aI_ray" and w_ne: "w \<noteq> []"
      and y: "y = a_elt \<otimes>\<^bsub>F2\<^esub> w"
      by auto
    from w_ray obtain n where w: "w = replicate n (True, A)"
      unfolding aI_ray_def by blast
    from w_ne w obtain m where n: "n = Suc m"
      by (cases n) auto
    have w_S: "w \<in> S_aI"
      using aI_ray_cases[OF w_ray] w_ne by blast
    have "y = tl w"
      using a_mult_starts_with_aI[OF w_S] y by simp
    also have "\<dots> = replicate m (True, A)"
      using w n by simp
    finally show "y \<in> aI_ray"
      unfolding aI_ray_def by blast
  qed
  show "aI_ray \<subseteq> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` (aI_ray - {[]})"
  proof
    fix y
    assume "y \<in> aI_ray"
    then obtain n where y: "y = replicate n (True, A)"
      unfolding aI_ray_def by blast
    let ?w = "replicate (Suc n) (True, A)"
    have w_ray: "?w \<in> aI_ray"
      unfolding aI_ray_def by blast
    have w_ne: "?w \<noteq> []"
      by simp
    have w_S: "?w \<in> S_aI"
      using aI_ray_cases[OF w_ray] w_ne by blast
    have "a_elt \<otimes>\<^bsub>F2\<^esub> ?w = tl ?w"
      by (rule a_mult_starts_with_aI[OF w_S])
    also have "\<dots> = y"
      using y by simp
    finally show "y \<in> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` (aI_ray - {[]})"
      using w_ray w_ne by blast
  qed
qed

lemma a_mult_nonray_stays_nonray:
  assumes "w \<in> S_aI" and "w \<notin> aI_ray"
  shows "a_elt \<otimes>\<^bsub>F2\<^esub> w \<notin> aI_ray"
proof
  assume ray: "a_elt \<otimes>\<^bsub>F2\<^esub> w \<in> aI_ray"
  from assms(1) have w_ne: "w \<noteq> []" and w_hd: "hd w = (True, A)"
    and w_carrier: "w \<in> carrier F2"
    by (auto simp: starts_with_def)
  from w_ne w_hd obtain u where w: "w = (True, A) # u"
    by (cases w) auto
  have "tl w \<in> aI_ray"
    using ray a_mult_starts_with_aI[OF assms(1)] by simp
  then obtain n where u: "u = replicate n (True, A)"
    unfolding aI_ray_def using w by auto
  hence "w = replicate (Suc n) (True, A)"
    using w by simp
  hence "w \<in> aI_ray"
    unfolding aI_ray_def by blast
  with assms(2) show False
    by contradiction
qed

lemma image_a_S_aI_nonray:
  "(\<otimes>\<^bsub>F2\<^esub>) a_elt ` (S_aI - aI_ray) = carrier F2 - S_a - aI_ray"
proof
  show "(\<otimes>\<^bsub>F2\<^esub>) a_elt ` (S_aI - aI_ray) \<subseteq> carrier F2 - S_a - aI_ray"
  proof
    fix y
    assume "y \<in> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` (S_aI - aI_ray)"
    then obtain w where w: "w \<in> S_aI" "w \<notin> aI_ray"
      and y: "y = a_elt \<otimes>\<^bsub>F2\<^esub> w"
      by auto
    have "y \<in> carrier F2 - S_a"
      using image_a_S_aI w(1) y by blast
    moreover have "y \<notin> aI_ray"
      using a_mult_nonray_stays_nonray[OF w] y by simp
    ultimately show "y \<in> carrier F2 - S_a - aI_ray"
      by simp
  qed
  show "carrier F2 - S_a - aI_ray \<subseteq> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` (S_aI - aI_ray)"
  proof
    fix y
    assume y: "y \<in> carrier F2 - S_a - aI_ray"
    hence "y \<in> carrier F2 - S_a"
      by simp
    then obtain w where w: "w \<in> S_aI" and y_eq: "y = a_elt \<otimes>\<^bsub>F2\<^esub> w"
      using image_a_S_aI by blast
    have "w \<notin> aI_ray"
    proof
      assume w_ray: "w \<in> aI_ray"
      with w have "w \<in> aI_ray - {[]}"
        by (auto simp: starts_with_def)
      hence "y \<in> aI_ray"
        using y_eq a_mult_aI_ray_pos by blast
      with y show False
        by simp
    qed
    thus "y \<in> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` (S_aI - aI_ray)"
      using w y_eq by blast
  qed
qed

theorem F2_paradoxical_partition:
  "\<exists>P Q :: ((bool \<times> gen2) list) set list. \<exists>gP gQ :: ((bool \<times> gen2) list) list.
       length P = length gP \<and> length Q = length gQ \<and>
       set gP \<subseteq> carrier F2 \<and> set gQ \<subseteq> carrier F2 \<and>
       pairwise_disjoint (P @ Q) \<and>
       pairwise_disjoint (map2 F2_act.image_set gP P) \<and>
       pairwise_disjoint (map2 F2_act.image_set gQ Q) \<and>
       carrier F2 = (\<Union>i<length P. P ! i) \<union> (\<Union>i<length Q. Q ! i) \<and>
       carrier F2 = (\<Union>i<length P. F2_act.image_set (gP ! i) (P ! i)) \<and>
       carrier F2 = (\<Union>i<length Q. F2_act.image_set (gQ ! i) (Q ! i))"
proof -
  let ?A1 = "S_a \<union> aI_ray"
  let ?A2 = "S_aI - aI_ray"
  let ?B1 = "S_b"
  let ?B2 = "S_bI"
  let ?P = "[?A1, ?A2]"
  let ?Q = "[?B1, ?B2]"
  let ?gP = "[[]::(bool \<times> gen2) list, a_elt]"
  let ?gQ = "[[]::(bool \<times> gen2) list, b_elt]"

  have ray_disj_Sa: "aI_ray \<inter> S_a = {}"
    using aI_ray_cases starts_with_pairwise_disjoint by blast
  have ray_disj_Sb: "aI_ray \<inter> S_b = {}"
    using aI_ray_cases starts_with_pairwise_disjoint by blast
  have ray_disj_SbI: "aI_ray \<inter> S_bI = {}"
    using aI_ray_cases starts_with_pairwise_disjoint by blast

  have source_cover: "carrier F2 =
      (\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i)"
  proof
    show "carrier F2 \<subseteq> (\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i)"
    proof
      fix w
      assume w: "w \<in> carrier F2"
      show "w \<in> (\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i)"
      proof (cases "w \<in> S_a \<or> w \<in> S_aI \<or> w \<in> S_b \<or> w \<in> S_bI")
        case True
        then consider "w \<in> S_a" | "w \<in> S_aI" | "w \<in> S_b" | "w \<in> S_bI"
          by blast
        thus ?thesis
        proof cases
          case 1
          then show ?thesis by (simp add: lessThan_Suc)
        next
          case 2
          then show ?thesis
          proof (cases "w \<in> aI_ray")
            case True
            then show ?thesis by (simp add: lessThan_Suc)
          next
            case False
            with 2 show ?thesis by (simp add: lessThan_Suc)
          qed
        next
          case 3
          then show ?thesis by (simp add: lessThan_Suc)
        next
          case 4
          then show ?thesis by (simp add: lessThan_Suc)
        qed
      next
        case False
        with F2_decomposition w have "w = []"
          by blast
        hence "w \<in> aI_ray"
          unfolding aI_ray_def by (auto intro!: exI[of _ 0])
        thus ?thesis
          by (simp add: lessThan_Suc)
      qed
    qed
    show "(\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i) \<subseteq> carrier F2"
      using starts_with_subset[of False A] starts_with_subset[of True A]
        starts_with_subset[of False B] starts_with_subset[of True B]
        aI_ray_subset_carrier
      by (auto simp: lessThan_Suc)
  qed

  have source_disj: "pairwise_disjoint (?P @ ?Q)"
    using starts_with_pairwise_disjoint ray_disj_Sa ray_disj_Sb ray_disj_SbI
    by (auto simp: pairwise_disjoint_def nth_Cons' nth_append Int_commute)

  have im_P0: "F2_act.image_set ([]::(bool \<times> gen2) list) ?A1 = ?A1"
    using starts_with_subset aI_ray_subset_carrier
    by (intro F2_act.image_set_unit) auto
  have im_P1: "F2_act.image_set a_elt ?A2 = carrier F2 - S_a - aI_ray"
    by (simp add: F2_act.image_set_def image_a_S_aI_nonray)
  have im_Q0: "F2_act.image_set ([]::(bool \<times> gen2) list) ?B1 = ?B1"
    using starts_with_subset
    by (rule F2_act.image_set_unit)
  have im_Q1: "F2_act.image_set b_elt ?B2 = (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI"
    by (simp add: F2_act.image_set_def)

  have map2P: "map2 F2_act.image_set ?gP ?P = [?A1, carrier F2 - S_a - aI_ray]"
    using im_P0 im_P1 by simp
  have map2Q: "map2 F2_act.image_set ?gQ ?Q = [S_b, (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI]"
    using im_Q0 im_Q1 by simp

  have imageP_disj: "pairwise_disjoint (map2 F2_act.image_set ?gP ?P)"
    using map2P by (auto simp: pairwise_disjoint_def nth_Cons' Int_commute)
  have imageQ_disj: "pairwise_disjoint (map2 F2_act.image_set ?gQ ?Q)"
    using S_b_disj_image_b_S_bI map2Q
    by (auto simp: pairwise_disjoint_def nth_Cons' Int_commute)

  have coverP: "carrier F2 =
      (\<Union>i<length ?P. F2_act.image_set (?gP ! i) (?P ! i))"
  proof -
    have "(\<Union>i<length ?P. F2_act.image_set (?gP ! i) (?P ! i)) =
        ?A1 \<union> (carrier F2 - S_a - aI_ray)"
      using im_P0 im_P1 by (auto simp: lessThan_Suc nth_Cons')
    also have "\<dots> = carrier F2"
      using starts_with_subset aI_ray_subset_carrier by auto
    finally show ?thesis
      by simp
  qed

  have coverQ: "carrier F2 =
      (\<Union>i<length ?Q. F2_act.image_set (?gQ ! i) (?Q ! i))"
  proof -
    have "(\<Union>i<length ?Q. F2_act.image_set (?gQ ! i) (?Q ! i)) =
        S_b \<union> (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI"
      using im_Q0 im_Q1 by (auto simp: lessThan_Suc nth_Cons')
    also have "\<dots> = carrier F2"
      by (rule S_b_un_image_b_S_bI)
    finally show ?thesis
      by simp
  qed

  show ?thesis
  proof (intro exI conjI)
    show "length ?P = length ?gP"
      by simp
    show "length ?Q = length ?gQ"
      by simp
    show "set ?gP \<subseteq> carrier F2"
      by simp
    show "set ?gQ \<subseteq> carrier F2"
      by simp
    show "pairwise_disjoint (?P @ ?Q)"
      by (rule source_disj)
    show "pairwise_disjoint (map2 F2_act.image_set ?gP ?P)"
      by (rule imageP_disj)
    show "pairwise_disjoint (map2 F2_act.image_set ?gQ ?Q)"
      by (rule imageQ_disj)
    show "carrier F2 = (\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i)"
      by (rule source_cover)
    show "carrier F2 = (\<Union>i<length ?P. F2_act.image_set (?gP ! i) (?P ! i))"
      by (rule coverP)
    show "carrier F2 = (\<Union>i<length ?Q. F2_act.image_set (?gQ ! i) (?Q ! i))"
      by (rule coverQ)
  qed
qed

text \<open>
  We unfold @{const F2_act.paradoxical} directly to avoid locale-instantiation
  complications with implicit polymorphic variables.
\<close>

theorem F2_paradoxical:
  "F2_act.paradoxical (carrier F2)"
proof -
  let ?P = "[S_a, S_aI]" and ?Q = "[S_b, S_bI]"
  let ?gP = "[[]::(bool \<times> gen2) list, a_elt]"
  let ?gQ = "[[]::(bool \<times> gen2) list, b_elt]"

  have lensP: "length ?P = length ?gP" by simp
  have lensQ: "length ?Q = length ?gQ" by simp

  have closedP: "set ?gP \<subseteq> carrier F2" by simp
  have closedQ: "set ?gQ \<subseteq> carrier F2" by simp

  have disj_P: "S_a \<inter> S_aI = {}"
    by (simp add: starts_with_pairwise_disjoint)
  have disj_Q: "S_b \<inter> S_bI = {}"
    by (simp add: starts_with_pairwise_disjoint)
  have disj_PQ: "(S_a \<union> S_aI) \<inter> (S_b \<union> S_bI) = {}"
    using starts_with_pairwise_disjoint by blast

  have disj_all: "pairwise_disjoint (?P @ ?Q)"
    using disj_P disj_Q disj_PQ
    by (auto simp: pairwise_disjoint_def nth_Cons' nth_append Int_commute)

  have im_P0: "F2_act.image_set ([]::(bool \<times> gen2) list) S_a = S_a"
    using starts_with_subset
    by (rule F2_act.image_set_unit)
  have im_Q0: "F2_act.image_set ([]::(bool \<times> gen2) list) S_b = S_b"
    using starts_with_subset
    by (rule F2_act.image_set_unit)
  have im_P1: "F2_act.image_set a_elt S_aI = (\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI"
    by (simp add: F2_act.image_set_def)
  have im_Q1: "F2_act.image_set b_elt S_bI = (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI"
    by (simp add: F2_act.image_set_def)

  have map2P: "map2 F2_act.image_set ?gP ?P = [S_a, (\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI]"
    using im_P0 im_P1 by simp
  have map2Q: "map2 F2_act.image_set ?gQ ?Q = [S_b, (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI]"
    using im_Q0 im_Q1 by simp

  have disj_im_P: "pairwise_disjoint (map2 F2_act.image_set ?gP ?P)"
    using S_a_disj_image_a_S_aI map2P
    by (auto simp: pairwise_disjoint_def nth_Cons' Int_commute)
  have disj_im_Q: "pairwise_disjoint (map2 F2_act.image_set ?gQ ?Q)"
    using S_b_disj_image_b_S_bI map2Q
    by (auto simp: pairwise_disjoint_def nth_Cons' Int_commute)

  have un_sub: "(\<Union>i<length ?P. ?P ! i) \<union> (\<Union>i<length ?Q. ?Q ! i) \<subseteq> carrier F2"
    using starts_with_subset
    by (auto simp: lessThan_Suc nth_Cons')

  have cov_P: "carrier F2 = (\<Union>i<length ?P. F2_act.image_set (?gP ! i) (?P ! i))"
  proof -
    have "(\<Union>i<length ?P. F2_act.image_set (?gP ! i) (?P ! i))
        = F2_act.image_set [] S_a \<union> F2_act.image_set a_elt S_aI"
      by (auto simp: lessThan_Suc nth_Cons')
    also have "\<dots> = S_a \<union> (\<otimes>\<^bsub>F2\<^esub>) a_elt ` S_aI"
      using im_P0 im_P1 by simp
    also have "\<dots> = carrier F2" by (rule S_a_un_image_a_S_aI)
    finally show ?thesis by simp
  qed

  have cov_Q: "carrier F2 = (\<Union>i<length ?Q. F2_act.image_set (?gQ ! i) (?Q ! i))"
  proof -
    have "(\<Union>i<length ?Q. F2_act.image_set (?gQ ! i) (?Q ! i))
        = F2_act.image_set [] S_b \<union> F2_act.image_set b_elt S_bI"
      by (auto simp: lessThan_Suc nth_Cons')
    also have "\<dots> = S_b \<union> (\<otimes>\<^bsub>F2\<^esub>) b_elt ` S_bI"
      using im_Q0 im_Q1 by simp
    also have "\<dots> = carrier F2" by (rule S_b_un_image_b_S_bI)
    finally show ?thesis by simp
  qed

  show ?thesis
    unfolding F2_act.paradoxical_def
    using lensP lensQ closedP closedQ disj_all disj_im_P disj_im_Q
          un_sub cov_P cov_Q
    by blast
qed

end
