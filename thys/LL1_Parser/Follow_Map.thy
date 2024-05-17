section \<open>Follow map\<close>

theory Follow_Map
imports First_Map
begin

type_synonym ('n, 't) follow_map = "('n, 't lookahead list) fmap"

fun updateFo :: "'n set \<Rightarrow> ('n, 't) first_map \<Rightarrow> 'n \<Rightarrow> ('n, 't) rhs \<Rightarrow> ('n, 't) follow_map
    \<Rightarrow> ('n, 't) follow_map" where
  "updateFo nu fi lx [] fo = fo"
| "updateFo nu fi lx ((T _) # gamma') fo = updateFo nu fi lx gamma' fo"
| "updateFo nu fi lx ((NT rx) # gamma') fo = (let fo' = updateFo nu fi lx gamma' fo;
    lSet = findOrEmpty lx fo';
    rSet = firstGamma gamma' nu fi;
    additions = (if nullableGamma gamma' nu then lSet @@ rSet else rSet)
    in (case fmlookup fo' rx of
      None \<Rightarrow> (if additions = [] then fo' else fmupd rx additions fo')
    | Some rxFollow \<Rightarrow> (if set additions \<subseteq> set rxFollow then fo'
        else fmupd rx (rxFollow @@ additions) fo')))"

definition followPass :: "('n, 't) prods \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map \<Rightarrow> ('n, 't) follow_map
  \<Rightarrow> ('n, 't) follow_map" where
  "followPass ps nu fi fo = foldr (\<lambda>(x, gamma) fo. updateFo nu fi x gamma fo) ps fo"

partial_function (option) mkFollowMap' :: "('n, 't) grammar \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map
    \<Rightarrow> ('n, 't) follow_map \<Rightarrow> ('n, 't) follow_map option" where
  "mkFollowMap' g nu fi fo = (let fo' = followPass (prods g) nu fi fo in
    (if fo = fo' then Some fo else mkFollowMap' g nu fi fo'))"

abbreviation initial_fo :: "('n, 't) grammar \<Rightarrow> ('n, 't) follow_map" where
  "initial_fo g \<equiv> fmupd (start g) [EOF] fmempty"

definition mkFollowMap :: "('n, 't) grammar \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map
  \<Rightarrow> ('n, 't) follow_map" where
  "mkFollowMap g nu fi = the (mkFollowMap' g nu fi (initial_fo g))"


subsection \<open>Termination\<close>

fun ntsOfGamma :: "('n, 't) rhs \<Rightarrow> 'n set" where
  "ntsOfGamma [] = {}"
| "ntsOfGamma ((T _)#gamma') = ntsOfGamma gamma'"
| "ntsOfGamma ((NT x)#gamma') = insert x (ntsOfGamma gamma')"

definition ntsOf :: "('n, 't) grammar \<Rightarrow> 'n set" where
  "ntsOf g = {start g} \<union> fst ` set (prods g) \<union> \<Union>(ntsOfGamma ` snd ` set (prods g))"

fun lookaheadsOfGamma :: "('n, 't) rhs \<Rightarrow> 't lookahead set" where
  "lookaheadsOfGamma [] = {}"
| "lookaheadsOfGamma ((T x)#gamma') = insert (LA x) (lookaheadsOfGamma gamma') "
| "lookaheadsOfGamma ((NT _)#gamma') = lookaheadsOfGamma gamma'"

definition lookaheadsOf :: "('n, 't) grammar \<Rightarrow> 't lookahead set" where
  "lookaheadsOf g = {EOF} \<union> \<Union>(lookaheadsOfGamma ` snd ` set (prods g))"

definition all_pairs_are_follow_candidates ::
    "('n, 't) follow_map \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "all_pairs_are_follow_candidates fo g =
  (\<forall>(x, la) \<in> pairsOf fo. x \<in> ntsOf g \<and> la \<in> lookaheadsOf g)"

definition countFollowCands :: "('n, 't) grammar \<Rightarrow> ('n, 't) follow_map \<Rightarrow> nat" where
  "countFollowCands g fo =
  (let allCandidates = (ntsOf g) \<times> (lookaheadsOf g) in card (allCandidates - (pairsOf fo)))"


lemma followPass_cons[simp]:
  "followPass ((x, gamma) # ps) nu fi fo = updateFo nu fi x gamma (followPass ps nu fi fo)"
  unfolding followPass_def by auto

lemma medial_t_in_lookaheadsOf:
  "(x, gpre @ (T y) # gsuf) \<in> set (prods g) \<Longrightarrow> (LA y) \<in> lookaheadsOf g"
proof -
  assume A: "(x, gpre @ T y # gsuf) \<in> set (prods g)"
  have "LA y \<in> lookaheadsOfGamma (gpre @ T y # gsuf)"
  proof (induction gpre)
    case Nil
    then show ?case by auto
  next
    case (Cons a gpre)
    then show ?case by (cases a) (auto simp add: Cons.IH)
  qed
  then have "LA y \<in> \<Union> (lookaheadsOfGamma ` snd ` set (prods g))" using A image_def by fastforce
  then show "(LA y) \<in> lookaheadsOf g" unfolding lookaheadsOf_def by auto
qed

lemma first_sym_in_lookaheadsOf: "first_sym g la s \<Longrightarrow> s = NT x \<Longrightarrow> la \<in> lookaheadsOf g"
proof (induction arbitrary: x rule: first_sym.induct)
  case (FirstT y)
  then show ?case by auto
next
  case (FirstNT x' gpre s gsuf la)
  show ?case
  proof (cases s)
    case (NT _)
    then show ?thesis using FirstNT.IH by auto
  next
    case (T y)
    from FirstNT.hyps(3) have "la = LA y" using T by (auto elim: first_sym.cases)
    have "(x', gpre @ (T y) # gsuf) \<in> set (prods g)" using FirstNT.hyps(1) T by auto
    then have "(LA y) \<in> lookaheadsOf g" by - (rule medial_t_in_lookaheadsOf, auto)
    then show ?thesis using \<open>la = LA y\<close> by auto
  qed
qed

lemma first_map_la_in_lookaheadsOf:
  "first_map_for fi g \<Longrightarrow> fmlookup fi x = Some s \<Longrightarrow> la \<in> set s \<Longrightarrow> la \<in> lookaheadsOf g"
  unfolding first_map_sound_def by (rule first_sym_in_lookaheadsOf[where s = "NT x"], auto)

lemma in_firstGamma_in_lookaheadsOf:
  "first_map_for fi g \<Longrightarrow> (x, gpre @ gsuf) \<in> set (prods g) \<Longrightarrow> la \<in> set (firstGamma gsuf nu fi)
  \<Longrightarrow> la \<in> lookaheadsOf g"
proof (induction gsuf arbitrary: gpre)
  case Nil
  then show ?case by auto
next
  case (Cons s gsuf)
  have "la \<in> set (if nullableSym s nu then firstSym s fi @@ firstGamma gsuf nu fi
      else firstSym s fi)"
    using Cons.prems(3) by auto
  then consider (la_in_firstSym) "la \<in> set (firstSym s fi)"
    | (la_in_firstGamma) "la \<in> set (firstGamma gsuf nu fi)"
    by (auto split: if_splits)
  then show ?case
  proof cases
    case la_in_firstSym
    then show ?thesis
    proof (cases s)
      case (NT x)
      then obtain s where "fmlookup fi x = Some s" and "la \<in> set s"
        using in_findOrEmpty_exists_set la_in_firstSym by fastforce
      with Cons.prems(1) show ?thesis by (rule first_map_la_in_lookaheadsOf[where ?s = "s"])
    next
      case (T x)
      then show ?thesis
        using Cons.prems(2) la_in_firstSym medial_t_in_lookaheadsOf by fastforce
    qed
  next
    case la_in_firstGamma
    then show ?thesis using Cons.prems by - (rule Cons.IH[where ?gpre = "gpre @ [s]"], auto)
  qed
qed

lemma la_in_fo_in_lookaheadsOf: "fmlookup fo x = Some xFollow \<Longrightarrow> la \<in> set xFollow
  \<Longrightarrow> all_pairs_are_follow_candidates fo g \<Longrightarrow> la \<in> lookaheadsOf g"
proof -
  assume "fmlookup fo x = Some xFollow" "la \<in> set xFollow" "all_pairs_are_follow_candidates fo g"
  then have "la \<in> set (findOrEmpty x fo)" by (simp add: findOrEmpty_def)
  then have "(x, la) \<in> pairsOf fo" by (simp add: in_findOrEmpty_iff_in_pairsOf)
  with \<open>all_pairs_are_follow_candidates fo g\<close> show ?thesis
    unfolding all_pairs_are_follow_candidates_def by auto
qed

lemma medial_nt_in_ntsOfGamma: "x \<in> ntsOfGamma (gpre @ (NT x) # gsuf)"
proof (induction gpre)
  case Nil
  then show ?case by auto
next
  case (Cons a gpre)
  then show ?case
  proof (cases a)
    case (NT y)
    then show ?thesis unfolding ntsOf_def by (simp add: Cons.IH)
  next
    case (T _)
    then show ?thesis by (simp add: Cons.IH)
  qed
qed

lemma medial_nt_in_ntsOf: "(lx, gpre @ (NT rx) # gsuf) \<in> set (prods g) \<Longrightarrow> rx \<in> (ntsOf g)"
proof (induction "prods g")
  case Nil
  then show ?case by auto
next
  case (Cons a x)
  then show ?case unfolding ntsOf_def using medial_nt_in_ntsOfGamma by fastforce
qed

lemma updateFo_induct_refined:
  fixes nu :: "'n set"
    and lx :: "'n"
    and gamma' :: "('n, 't) symbol list"
    and fi :: "('n, 't) first_map"
    and fo :: "('n, 't) follow_map"
    and P :: "'n set \<Rightarrow> ('n, 't) first_map \<Rightarrow> 'n \<Rightarrow> ('n, 't) symbol list \<Rightarrow> ('n, 't) follow_map
      \<Rightarrow> bool"
  defines "additions \<equiv> (\<lambda>nu fi lx gamma' fo. (if nullableGamma gamma' nu
      then findOrEmpty lx (updateFo nu fi lx gamma' fo) @@ (firstGamma gamma' nu fi)
      else firstGamma gamma' nu fi))"
  assumes Nil: "(\<And>nu fi lx fo. P nu fi lx [] fo)"
    and T: "(\<And>nu fi lx y gamma' fo. P nu fi lx gamma' fo \<Longrightarrow> P nu fi lx (T y # gamma') fo)"
    and NT_None_same: "(\<And>nu fi lx rx gamma' fo. P nu fi lx gamma' fo
      \<Longrightarrow> fmlookup (updateFo nu fi lx gamma' fo) rx = None \<Longrightarrow> additions nu fi lx gamma' fo = []
      \<Longrightarrow> P nu fi lx (NT rx # gamma') fo)"
    and NT_None_new: "(\<And>nu fi lx rx gamma' fo. P nu fi lx gamma' fo
      \<Longrightarrow> fmlookup (updateFo nu fi lx gamma' fo) rx = None \<Longrightarrow> additions nu fi lx gamma' fo \<noteq> []
      \<Longrightarrow> P nu fi lx (NT rx # gamma') fo)"
    and NT_Some_same: "(\<And>nu fi lx rx gamma' fo rxFollow. P nu fi lx gamma' fo
      \<Longrightarrow> fmlookup (updateFo nu fi lx gamma' fo) rx = Some rxFollow
      \<Longrightarrow> set (additions nu fi lx gamma' fo) \<subseteq> set rxFollow \<Longrightarrow> P nu fi lx (NT rx # gamma') fo)"
    and NT_Some_new: "(\<And>nu fi lx rx gamma' fo rxFollow. P nu fi lx gamma' fo
      \<Longrightarrow> fmlookup (updateFo nu fi lx gamma' fo) rx = Some rxFollow
      \<Longrightarrow> \<not> set (additions nu fi lx gamma' fo) \<subseteq> set rxFollow \<Longrightarrow> P nu fi lx (NT rx # gamma') fo)"
  shows "P (nu::'n set) fi lx (gamma :: ('n, 't) symbol list) fo"
  unfolding additions_def
proof (rule updateFo.induct[where ?P = "P"])
  fix nu fi lx fo rx gamma'
  assume "P nu fi lx gamma' fo"
  let ?fo' = "updateFo nu fi lx gamma' fo"
  consider "fmlookup ?fo' rx = None" "additions nu fi lx gamma' fo = []"
    | "fmlookup ?fo' rx = None" "additions nu fi lx gamma' fo \<noteq> []"
    | rxFollow where "fmlookup ?fo' rx = Some rxFollow"
        and "set (additions nu fi lx gamma' fo) \<subseteq> set rxFollow"
      | rxFollow where "fmlookup ?fo' rx = Some rxFollow"
        and "\<not> set (additions nu fi lx gamma' fo) \<subseteq> set rxFollow"
    by blast
  then show "P nu fi lx (NT rx # gamma') fo" by
    (cases) (auto simp add: \<open>P nu fi lx gamma' fo\<close> assms)
qed (auto simp add: Nil T)

lemma updateFo_preserves_apac_fmupd_additions: assumes "first_map_for fi g"
  and "all_pairs_are_follow_candidates (updateFo nu fi lx gamma' fo) g"
  and "(lx, gpre @ NT rx # gamma') \<in> set (prods g)"
  and "la \<in> set (if nullableGamma gamma' nu then (findOrEmpty lx (updateFo nu fi lx gamma' fo))
    @@ (firstGamma gamma' nu fi) else firstGamma gamma' nu fi)"
  shows "rx \<in> ntsOf g \<and> la \<in> lookaheadsOf g"
proof
  show "rx \<in> ntsOf g" by (meson assms(3) medial_nt_in_ntsOf)
next
  from assms(4) consider
      (la_in_findOrEmpty) "la \<in> set (findOrEmpty lx (updateFo nu fi lx gamma' fo))"
      | (la_in_firstGamma) "la \<in> set (firstGamma gamma' nu fi)"
    by (auto split: if_splits)
  then show "la \<in> lookaheadsOf g"
  proof (cases)
    case la_in_findOrEmpty
    then obtain lxFollow where "fmlookup (updateFo nu fi lx gamma' fo) lx = Some lxFollow"
      "la \<in> set lxFollow" using in_findOrEmpty_exists_set assms(3) by fast
    then show ?thesis by (auto intro: la_in_fo_in_lookaheadsOf simp add: assms(2))
  next
    case la_in_firstGamma
    with assms(1,3) show ?thesis by
      (auto intro: in_firstGamma_in_lookaheadsOf[where gpre = "gpre @ [NT rx]"])
  qed
qed

lemma updateFo_preserves_apac:
  "first_map_for fi g \<Longrightarrow> (lx, gpre @ gsuf) \<in> set (prods g)
  \<Longrightarrow> all_pairs_are_follow_candidates fo g
  \<Longrightarrow> all_pairs_are_follow_candidates (updateFo nu fi lx gsuf fo) g"
proof (induction nu fi lx gsuf fo arbitrary: gpre rule: updateFo_induct_refined)
  case (1 nu fi lx fo)
  then show ?case by simp
next
  case (2 nu fi lx y gamma' fo)
  from 2(2-) show ?case by (auto intro: 2(1)[where gpre = "gpre @ [T y]"])
next
  case (3 nu fi lx rx gamma' fo)
  from 3(2-) have "all_pairs_are_follow_candidates (updateFo nu fi lx gamma' fo) g" by
    (auto intro: 3(1)[where gpre = "gpre @ [NT rx]"])
  then show ?case by (simp add: "3.hyps")
next
  case (4 nu fi lx rx gamma' fo)
  let ?fo' = "updateFo nu fi lx gamma' fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gamma' nu fi"
  let ?additions = "if nullableGamma gamma' nu then ?lSet @@ ?rSet else ?rSet"
  have IH: "all_pairs_are_follow_candidates ?fo' g" by
    (auto intro: "4.IH"[where ?gpre = "gpre @ [NT rx]"] simp add: "4.prems")
  have "x \<in> ntsOf g \<and> la \<in> lookaheadsOf g"
    if "(x ,la) \<in> pairsOf (fmupd rx ?additions ?fo')" for x la
  proof (cases "x = rx")
    case True
    then have "(lx, gpre @ NT x # gamma') \<in> set (prods g)" by (auto simp add: "4.prems"(2))
    moreover have "la \<in> set ?additions" using that by (simp only: True in_add_keys[symmetric])
    ultimately show ?thesis using "4.prems"(1,2) IH by
      - (rule updateFo_preserves_apac_fmupd_additions)
  next
    case False
    then have "(x, la) \<in> pairsOf ?fo'" by (metis in_add_keys_neq that)
    then show ?thesis using IH all_pairs_are_follow_candidates_def by fastforce
  qed
  then show ?case unfolding all_pairs_are_follow_candidates_def by (auto simp add: 4 Let_def)
next
  case (5 nu fi lx rx gamma' fo rxFollow)
  from 5(2-) have "all_pairs_are_follow_candidates (updateFo nu fi lx gamma' fo) g" by
    (auto intro: 5(1)[where gpre = "gpre @ [NT rx]"])
  then show ?case by (simp add: "5.hyps")
next
  case (6 nu fi lx rx gamma' fo rxFollow)
  let ?fo' = "updateFo nu fi lx gamma' fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gamma' nu fi"
  let ?additions = "if nullableGamma gamma' nu then ?lSet @@ ?rSet else ?rSet"
  have IH: "all_pairs_are_follow_candidates ?fo' g"
    by (auto intro: "6.IH"[where ?gpre = "gpre @ [NT rx]"] simp add: "6.prems")
  have "x \<in> ntsOf g \<and> la \<in> lookaheadsOf g"
    if "(x ,la) \<in> pairsOf (fmupd rx (rxFollow @@ ?additions) ?fo')" for x la
  proof (cases "x = rx")
    case True
    from that have "la \<in> set (rxFollow @@ ?additions)" by (simp only: True in_add_keys[symmetric])
    then consider (la_in_rxFollow) "la \<in> set rxFollow" | (la_in_additions) "la \<in> set ?additions" by
        auto
    then show ?thesis
    proof (cases)
      case la_in_rxFollow
      then show ?thesis
        using "6.hyps"(1) "6.prems"(2) IH True la_in_fo_in_lookaheadsOf medial_nt_in_ntsOf
        by fastforce
    next
      case la_in_additions
      then show ?thesis using "6.prems"(1,2) IH True updateFo_preserves_apac_fmupd_additions by
        fastforce
    qed
  next
    case False
    then have "(x, la) \<in> pairsOf ?fo'" by (metis in_add_keys_neq that)
    then show ?thesis using IH all_pairs_are_follow_candidates_def by fastforce
  qed
  then show ?case unfolding all_pairs_are_follow_candidates_def by (auto simp add: 6 Let_def)
qed

lemma followPass_preserves_apac': "first_map_for fi g \<Longrightarrow> pre @ suf = (prods g)
  \<Longrightarrow> all_pairs_are_follow_candidates fo g
  \<Longrightarrow> all_pairs_are_follow_candidates (followPass suf nu fi fo) g"
proof (induction suf arbitrary: pre)
  case Nil
  show ?case unfolding followPass_def by (simp add: Nil.prems(3))
next
  case (Cons a suf)
  obtain x gamma where "a = (x, gamma)" by fastforce
  have IH: "all_pairs_are_follow_candidates (followPass suf nu fi fo) g"
    using Cons.IH[where pre = "pre @ [a]"] Cons.prems by auto
  have "(x, gamma) \<in> set (prods g)" by
    (metis \<open>a = (x, gamma)\<close>[symmetric] in_set_conv_decomp Cons.prems(2))
  have "all_pairs_are_follow_candidates (updateFo nu fi x gamma (followPass suf nu fi fo)) g"
    using Cons.prems(1) \<open>(x, gamma) \<in> set (prods g)\<close> IH
    by - (rule updateFo_preserves_apac[where gpre = "[]"], auto)
  then show ?case by (simp add: \<open>a = (x, gamma)\<close>)
qed

lemma followPass_preserves_apac: "first_map_for fi g \<Longrightarrow> all_pairs_are_follow_candidates fo g
   \<Longrightarrow> all_pairs_are_follow_candidates (followPass (prods g) nu fi fo) g"
  by (rule followPass_preserves_apac'[where pre = "[]"]) auto

lemma updateFo_subset: "pairsOf fo \<subseteq> pairsOf (updateFo nu fi x' gamma fo)"
proof (induction nu fi x' gamma fo rule: updateFo_induct_refined)
  case (4 nu fi lx rx gamma' fo)
  let ?fo' = "updateFo nu fi lx gamma' fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gamma' nu fi"
  let ?additions = "(if nullableGamma gamma' nu then ?lSet @@ ?rSet else ?rSet)"
  have "(x, la) \<in> pairsOf (fmupd rx ?additions ?fo')" if "(x, la) \<in> pairsOf fo" for x la
  proof (cases "x = rx")
    case True
    then show ?thesis using "4.IH" "4.hyps"(1) True that by
      (fastforce simp add: in_pairsOf_exists)
  next
    case False
    have "(x, la) \<in> pairsOf ?fo'" using "4.IH" that by auto
    then show ?thesis using in_add_keys_neq[where ?fi = "?fo'"] False by auto
  qed
  then show ?case by (auto simp add: Let_def 4)
next
  case (6 nu fi lx rx gamma' fo rxFollow)
  let ?fo' = "updateFo nu fi lx gamma' fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gamma' nu fi"
  let ?additions = "(if nullableGamma gamma' nu then ?lSet @@ ?rSet else ?rSet)"
  have "(x, la) \<in> pairsOf (fmupd rx (rxFollow @@ ?additions) ?fo')"
    if "(x, la) \<in> pairsOf fo" for x la
  proof (cases "x = rx")
    case True
    have "la \<in> set (rxFollow @@ ?additions)" using "6.IH" "6.hyps"(1) True that by
      (fastforce simp add: in_pairsOf_exists)
    then show ?thesis using in_add_keys[where ?fi = "?fo'"] True by auto
  next
    case False
    have "(x, la) \<in> pairsOf ?fo'" using "6.IH" that by auto
    then show ?thesis using in_add_keys_neq[where ?fi = "?fo'"] False by auto
  qed
  then show ?case by (auto simp add: Let_def 6)
qed auto

lemma followPass_subset: "pairsOf fo \<subseteq> pairsOf (followPass ps nu fi fo)"
proof (induction ps)
  case Nil
  then show ?case by (simp add: followPass_def)
next
  case (Cons p ps)
  obtain x gamma where "p = (x, gamma)" by fastforce
  have "pairsOf (followPass ps nu fi fo)
    \<subseteq> pairsOf (updateFo nu fi x gamma (followPass ps nu fi fo))" using updateFo_subset by fast
  then have "pairsOf fo \<subseteq> pairsOf (updateFo nu fi x gamma (followPass ps nu fi fo))"
    using Cons.IH by blast
  then show ?case unfolding followPass_def by (simp add: \<open>p = (x, gamma)\<close>)
qed

lemma updateFo_not_equiv_exists': "first_map_for fi g \<Longrightarrow>(lx, gpre @ gsuf) \<in> set (prods g)
  \<Longrightarrow> all_pairs_are_follow_candidates fo g
  \<Longrightarrow> fo \<noteq> (updateFo nu fi lx gsuf fo)
  \<Longrightarrow> \<exists>x' la. x' \<in> ntsOf g \<and> la \<in> lookaheadsOf g \<and> (x', la) \<notin> pairsOf fo
    \<and> (x', la) \<in> pairsOf (updateFo nu fi lx gsuf fo)"
proof (induction nu fi lx gsuf fo arbitrary: gpre rule: updateFo_induct_refined)
  case (1 nu fi lx fo)
  then show ?case by simp
next
  case (2 nu fi lx y gsuf fo)
  have "\<exists>x' la. x' \<in> ntsOf g \<and> la \<in> lookaheadsOf g \<and> (x', la) \<notin> pairsOf fo
    \<and> (x', la) \<in> pairsOf (updateFo nu fi lx gsuf fo)" using "2.prems"
    by - (rule "2.IH"[where ?gpre = "gpre @ [T y]"], auto)
  then show ?case by (simp only: updateFo.simps)
next
  case (3 nu fi lx rx gsuf fo)
  from "3.prems"(4) have "fo \<noteq> updateFo nu fi lx gsuf fo" by (simp add: "3.hyps"(1) "3.hyps"(2))
  then have "\<exists>x' la. x' \<in> ntsOf g \<and> la \<in> lookaheadsOf g \<and> (x', la) \<notin> pairsOf fo
    \<and> (x', la) \<in> pairsOf (updateFo nu fi lx gsuf fo)" using "3.prems"(1,2,3)
    by - (rule "3.IH"[where ?gpre = "gpre @ [NT rx]"], auto)
  then show ?case by (simp add: "3.hyps"(1) "3.hyps"(2))
next
  case (4 nu fi lx rx gsuf fo)
  let ?fo' = "updateFo nu fi lx gsuf fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gsuf nu fi"
  let ?additions = "(if nullableGamma gsuf nu then ?lSet @@ ?rSet else ?rSet)"
  obtain la where "la \<in> set ?additions" using "4.hyps"(2) list.set_sel(1) by auto
  have "rx \<in> ntsOf g \<and> la \<in> lookaheadsOf g" "(rx, la) \<notin> pairsOf fo"
    "(rx, la) \<in> pairsOf (updateFo nu fi lx (NT rx # gsuf) fo)"
  proof -
    have "all_pairs_are_follow_candidates ?fo' g" using "4.prems"(1,2,3) by
      (auto intro: updateFo_preserves_apac[where ?gpre = "gpre @ [NT rx]"])
    then show "rx \<in> ntsOf g \<and> la \<in> lookaheadsOf g" using "4.prems"(1,2) \<open>la \<in> set ?additions\<close> by
      - (rule updateFo_preserves_apac_fmupd_additions)
  next
    have "(rx, la) \<notin> pairsOf ?fo'" using "4.hyps"(1) by (fastforce simp add: in_pairsOf_exists)
    then show "(rx, la) \<notin> pairsOf fo" using updateFo_subset by fastforce
  next
    have "(rx, la) \<in> pairsOf (fmupd rx ?additions ?fo')" using \<open>la \<in> set ?additions\<close> in_add_keys by
        fast
    then show "(rx, la) \<in> pairsOf (updateFo nu fi lx (NT rx # gsuf) fo)" by (simp add: 4 Let_def)
  qed
  then show ?case by auto
next
  case (5 nu fi lx rx gsuf fo rxFollow)
  from "5.prems"(4) have "fo \<noteq> updateFo nu fi lx gsuf fo" by (simp add: "5.hyps"(1) "5.hyps"(2))
  then have "\<exists>x' la. x' \<in> ntsOf g \<and> la \<in> lookaheadsOf g \<and> (x', la) \<notin> pairsOf fo
    \<and> (x', la) \<in> pairsOf (updateFo nu fi lx gsuf fo)"
    using "5.prems"(1,2,3) by - (rule "5.IH"[where ?gpre = "gpre @ [NT rx]"], auto)
  then show ?case by (simp add: "5.hyps"(1,2))
next
  case (6 nu fi lx rx gsuf fo rxFollow)
  let ?fo' = "updateFo nu fi lx gsuf fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gsuf nu fi"
  let ?additions = "(if nullableGamma gsuf nu then ?lSet @@ ?rSet else ?rSet)"
  obtain la where "la \<in> set ?additions" "la \<notin> set rxFollow" using "6.hyps"(2) by auto
  have "rx \<in> ntsOf g \<and> la \<in> lookaheadsOf g" "(rx, la) \<notin> pairsOf fo"
    "(rx, la) \<in> pairsOf (updateFo nu fi lx (NT rx # gsuf) fo)"
  proof -
    have "all_pairs_are_follow_candidates ?fo' g" using "6.prems"(1,2,3) by
      (auto intro: updateFo_preserves_apac[where ?gpre = "gpre @ [NT rx]"])
    then show "rx \<in> ntsOf g \<and> la \<in> lookaheadsOf g" using "6.prems"(1,2) \<open>la \<in> set ?additions\<close> by
      - (rule updateFo_preserves_apac_fmupd_additions)
  next
    have "(rx, la) \<notin> pairsOf ?fo'" using \<open>la \<notin> set rxFollow\<close> "6.hyps"(1) by
      (fastforce simp add: in_pairsOf_exists)
    then show "(rx, la) \<notin> pairsOf fo" using updateFo_subset by fastforce
  next
    have "la \<in> set (rxFollow @@ ?additions)" using \<open>la \<in> set ?additions\<close> by simp
    then have "(rx, la) \<in> pairsOf (fmupd rx (rxFollow @@ ?additions) ?fo')"
      using \<open>la \<in> set ?additions\<close> in_add_keys by fast
    then show "(rx, la) \<in> pairsOf (updateFo nu fi lx (NT rx # gsuf) fo)" by (simp add: 6 Let_def)
  qed
  then show ?case by auto
qed

lemma updateFo_not_equiv_exists: "first_map_for fi g \<Longrightarrow>(lx, gamma) \<in> set (prods g)
  \<Longrightarrow> all_pairs_are_follow_candidates fo g
  \<Longrightarrow> fo \<noteq> (updateFo nu fi lx gamma fo)
  \<Longrightarrow> \<exists>x' la. x' \<in> ntsOf g \<and> la \<in> lookaheadsOf g \<and> (x', la) \<notin> pairsOf fo
    \<and> (x', la) \<in> pairsOf (updateFo nu fi lx gamma fo)"
  by (rule updateFo_not_equiv_exists'[where gpre = "[]"]) auto

lemma followPass_equiv_or_exists': "first_map_for fi g \<Longrightarrow> all_pairs_are_follow_candidates fo g
  \<Longrightarrow> pre @ suf = (prods g) \<Longrightarrow> fo \<noteq> (followPass suf nu fi fo)
  \<Longrightarrow> (\<exists>x la. x \<in> (ntsOf g) \<and> la \<in> (lookaheadsOf g) \<and> (x, la) \<notin> (pairsOf fo)
    \<and> (x, la) \<in> (pairsOf (followPass suf nu fi fo)))"
proof (induction suf arbitrary: pre fo)
  case Nil
  have "fo = followPass [] nu fi fo" by (simp add: followPass_def)
  then show ?case using Nil.prems(4) by blast
next
  case (Cons a suf)
  obtain x gamma where "a = (x, gamma)" by fastforce
  show ?case
  proof (cases "fo \<noteq> followPass suf nu fi fo")
    case True
    then obtain x' la where "x' \<in> ntsOf g" "la \<in> lookaheadsOf g" "(x', la) \<notin> pairsOf fo"
      "(x', la) \<in> pairsOf (followPass suf nu fi fo)"
      using Cons.IH[of fo "pre @ [a]"] Cons.prems(1,2,3) by auto
    moreover have "(x', la) \<in> pairsOf (followPass (a # suf) nu fi fo)"
      using updateFo_subset \<open>(x', la) \<in> pairsOf (followPass suf nu fi fo)\<close>
      by (simp add: \<open>a = (x, gamma)\<close>) fast
    ultimately show ?thesis by blast
  next
    case False
    have A2: "(x, gamma) \<in> set (prods g)" by
      (metis \<open>a = (x, gamma)\<close> in_set_conv_decomp Cons.prems(3))
    have A3: "all_pairs_are_follow_candidates (followPass suf nu fi fo) g" using Cons.prems by
      - (rule followPass_preserves_apac'[where pre = "pre @ [a]"], auto)
    then have "followPass suf nu fi fo \<noteq> followPass (a # suf) nu fi fo" using False by
      (auto simp add: Cons.prems(4))
    then have A4: "followPass suf nu fi fo \<noteq> updateFo nu fi x gamma (followPass suf nu fi fo)"
      using False by (simp add: \<open>a = (x, gamma)\<close>)
    have "(\<exists>x' la. x' \<in> ntsOf g \<and> la \<in> lookaheadsOf g
        \<and> (x', la) \<notin> pairsOf (followPass suf nu fi fo)
        \<and> (x', la) \<in> pairsOf (updateFo nu fi x gamma (followPass suf nu fi fo)))"
      using Cons.prems(1) A2 A3 A4 by - (rule updateFo_not_equiv_exists, auto)
    then show ?thesis using False by (auto simp add: \<open>a = (x, gamma)\<close>)
  qed
qed

lemma followPass_not_equiv_exists: "first_map_for fi g \<Longrightarrow> all_pairs_are_follow_candidates fo g
    \<Longrightarrow> fo \<noteq> followPass (prods g) nu fi fo \<Longrightarrow> \<exists>x la. x \<in> ntsOf g \<and> la \<in> lookaheadsOf g
    \<and> (x, la) \<notin> pairsOf fo \<and> (x, la) \<in> pairsOf (followPass (prods g) nu fi fo)"
  using followPass_equiv_or_exists' by fastforce

lemma finite_ntsOfGamma: "finite (ntsOfGamma gamma)"
proof (induction gamma)
  case Nil
  then show ?case by auto
next
  case (Cons a gamma)
  then show ?case by (cases a) auto
qed

lemma finite_ntsOf: "finite (ntsOf g)"
  unfolding ntsOf_def by (simp add: finite_ntsOfGamma)

lemma finite_lookaheadsOfGamma: "finite (lookaheadsOfGamma gamma)"
proof (induction gamma)
  case Nil
  then show ?case by auto
next
  case (Cons a gamma)
  then show ?case by (cases a) auto
qed

lemma finite_lookaheadsOf: "finite (lookaheadsOf g)"
  unfolding lookaheadsOf_def by (simp add: finite_lookaheadsOfGamma)

lemma finite_allCandidates_follow: "finite (ntsOf g \<times> lookaheadsOf g)"
  using finite_lookaheadsOf finite_ntsOf by auto

lemma followPass_not_equiv_candidates_lt:
  "first_map_for fi g \<Longrightarrow> all_pairs_are_follow_candidates fo g
  \<Longrightarrow> fo \<noteq> (followPass (prods g) nu fi fo)
  \<Longrightarrow> countFollowCands g (followPass (prods g) nu fi fo) < countFollowCands g fo"
  unfolding countFollowCands_def Let_def
proof (rule psubset_card_mono)
  show "finite (ntsOf g \<times> lookaheadsOf g - pairsOf fo)" using finite_allCandidates_follow by auto
next
  assume "first_map_for fi g" "all_pairs_are_follow_candidates fo g"
    "fo \<noteq> (followPass (prods g) nu fi fo)"
  then obtain x la where "x \<in> ntsOf g \<and> la \<in> lookaheadsOf g \<and> (x, la) \<notin> pairsOf fo
    \<and> (x, la) \<in> pairsOf (followPass (prods g) nu fi fo)" using followPass_not_equiv_exists by blast
  then show "ntsOf g \<times> lookaheadsOf g - pairsOf (followPass (prods g) nu fi fo)
    \<subset> ntsOf g \<times> lookaheadsOf g - pairsOf fo" using followPass_subset by fastforce
qed

text\<open>Termination proof for mkFollowMap' with the assumption that fi is a correct first map, and
all\_pairs\_are\_follow\_candidates holds in the beginning and thus for every other iteration\<close>

lemma mkFollowMap'_dom_if_apac: "mkFollowMap' g nu fi fo \<noteq> None"
  if "first_map_for fi g" and "all_pairs_are_follow_candidates fo g"
  using that
proof (induction "(g, nu, fi, fo)" arbitrary: fi fo
    rule: measure_induct_rule[where f = "\<lambda>(g, nu, fi, fo). countFollowCands g fo"])
  case (less fi fo)
  have "fo \<noteq> followPass (prods g) nu fi fo
    \<Longrightarrow> countFollowCands g (followPass (prods g) nu fi fo)  < countFollowCands g fo"
    using less.prems by (simp add: followPass_not_equiv_candidates_lt)
  moreover have "fo \<noteq> followPass (prods g) nu fi fo
    \<Longrightarrow> all_pairs_are_follow_candidates (followPass (prods g) nu fi fo) g" using less.prems
    by - (rule followPass_preserves_apac)
  ultimately have "fo \<noteq> followPass (prods g) nu fi fo
    \<Longrightarrow> mkFollowMap' g nu fi (followPass (prods g) nu fi fo) \<noteq> None" by (simp add: less)
  then show ?case
    by (cases "fo \<noteq> followPass (prods g) nu fi fo") (auto simp add: mkFollowMap'.simps)
qed

lemma initial_fo_apac: "all_pairs_are_follow_candidates (initial_fo g) g"
  unfolding all_pairs_are_follow_candidates_def
proof
  fix a
  assume A: "a \<in> pairsOf (initial_fo g)"
  show "case a of (x, la) \<Rightarrow> x \<in> ntsOf g \<and> la \<in> lookaheadsOf g"
  proof
    fix x la
    assume "a = (x, la)"
    show "x \<in> ntsOf g \<and> la \<in> lookaheadsOf g"
    proof (cases "x = start g")
      case True
      have "la = EOF" using A True \<open>a = (x, la)\<close> by (fastforce simp add: in_add_value)
      then show ?thesis unfolding ntsOf_def lookaheadsOf_def by (simp add: \<open>x = start g\<close>)
    next
      case False
      then show ?thesis using A \<open>a = (x, la)\<close> by (fastforce simp add: in_pairsOf_exists)
    qed
  qed
qed


subsection \<open>Correctness Definitions\<close>

definition follow_map_sound :: "('n, 't) follow_map \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "follow_map_sound fo g =
  (\<forall>x la xFollow. fmlookup fo x = Some xFollow \<and> la \<in> set xFollow \<longrightarrow> follow_sym g la (NT x))"

definition follow_map_complete :: "('n, 't) follow_map \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "follow_map_complete fo g = (\<forall>la s x. follow_sym g la s \<and> s = NT x
  \<longrightarrow> (\<exists>xFollow. fmlookup fo x = Some xFollow \<and> la \<in> set xFollow))"

abbreviation follow_map_for :: "('n, 't) follow_map \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "follow_map_for fo g \<equiv> follow_map_sound fo g \<and> follow_map_complete fo g"


subsection \<open>Soundness\<close>

lemma first_gamma_tail_cons: "nullable_sym g s \<Longrightarrow> nullable_gamma g gpre \<Longrightarrow> first_gamma g la gsuf
    \<Longrightarrow> first_gamma g la (gpre @ s # gsuf)"
proof -
  assume "nullable_sym g s" "nullable_gamma g gpre" "first_gamma g la gsuf"
  obtain s' gpre' gsuf' where "nullable_gamma g gpre'" "first_sym g la s'"
    "gsuf = gpre' @ s' # gsuf'" using \<open>first_gamma g la gsuf\<close> by cases blast
  have "nullable_gamma g [s]" using \<open>nullable_sym g s\<close> by (simp add: NullableCons NullableNil)
  then have "nullable_gamma g ((gpre @ [s]) @ gpre')"
    using \<open>nullable_gamma g gpre'\<close> \<open>nullable_gamma g gpre\<close> nullable_app by blast
  then have "first_gamma g la ((gpre @ s # gpre') @ s' # gsuf')" using \<open>first_sym g la s'\<close> by
    - (rule FirstGamma, auto)
  then show "first_gamma g la (gpre @ s # gsuf)" by (simp add: \<open>gsuf = gpre' @ s' # gsuf'\<close>)
qed

lemma firstGamma_first_gamma: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> la \<in> set (firstGamma gamma nu fi) \<Longrightarrow> first_gamma g la gamma"
proof (induction gamma)
  case Nil
  then show ?case by (auto elim: first_gamma.cases)
next
  case (Cons s gamma)
  consider (la_in_firstSym) "la \<in> set (firstSym s fi)"
    | (la_in_firstGamma) "nullableSym s nu" "la \<in> set (firstGamma gamma nu fi)"
    using Cons.prems(3)
    by (metis firstGamma.simps(2) in_atleast1_list)
  then show ?case
  proof (cases)
    case la_in_firstSym
    have "first_sym g la s" using Cons.prems(2) la_in_firstSym by
      - (rule firstSym_first_sym[where fi = "fi"], auto)
    then show ?thesis using FirstGamma NullableNil by fastforce
  next
    case la_in_firstGamma
    then have "first_gamma g la gamma" using Cons.prems by - (rule Cons.IH)
    moreover have "nullable_sym g s"
      using nullableSym_nullable_sym Cons.prems(1) la_in_firstGamma(1) by blast
    ultimately have "first_gamma g la ([] @ s # gamma)" using NullableNil by
      - (rule first_gamma_tail_cons)
    then show ?thesis by auto
  qed
qed

lemma first_gamma_firstGamma: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> first_gamma g la gamma \<Longrightarrow> la \<in> set (firstGamma gamma nu fi)"
proof (induction gamma)
  case Nil
  then show ?case by (auto elim: first_gamma.cases)
next
  case (Cons s gamma)
  from Cons.prems(3) obtain s' gpre gsuf where "nullable_gamma g gpre" "first_sym g la s'"
    "gpre @ s' # gsuf = s # gamma" by (auto elim: first_gamma.cases)
  show ?case
  proof (cases gpre)
    case Nil
    then have "s = s'" "gsuf = gamma" using \<open>gpre @ s' # gsuf = s # gamma\<close> by auto
    then have "first_sym g la s" using \<open>first_sym g la s'\<close> by auto
    show ?thesis
    proof (cases s)
      case (NT x)
      from Cons.prems(2) obtain xFirst where "fmlookup fi x = Some xFirst" "la \<in> set xFirst"
        unfolding first_map_complete_def using \<open>first_sym g la s\<close> NT by fast
      then have "la \<in> set (firstGamma (gpre @ NT x # gsuf) nu fi)"
        using Cons.prems \<open>nullable_gamma g gpre\<close> by - (rule la_in_firstGamma_nt)
      then show ?thesis by (simp add: NT \<open>gsuf = gamma\<close> Nil)
    next
      case (T y)
      then show ?thesis using \<open>first_sym g la s\<close> by (auto elim: first_sym.cases)
    qed
  next
    case Cons_gpre: (Cons s'' gpre')
    have "s'' = s" "gpre' @ s' # gsuf = gamma"
      using \<open>gpre @ s' # gsuf = s # gamma\<close> Cons_gpre by auto
    from \<open>nullable_gamma g gpre\<close> have "nullable_gamma g gpre'" "nullable_sym g s''" using Cons_gpre
      by (auto elim: nullable_gamma.cases)
    show ?thesis
    proof (cases "nullableSym s nu")
      case True
      from \<open>nullable_gamma g gpre'\<close> have "first_gamma g la gamma" using \<open>first_sym g la s'\<close>
        by (auto intro: FirstGamma simp add: \<open>gpre' @ s' # gsuf = gamma\<close>[symmetric])
      then have "la \<in> set (firstGamma gamma nu fi)" using Cons.prems(1,2) by (auto intro: Cons.IH)
      then show ?thesis by (simp add: True)
    next
      case False
      from \<open>nullable_sym g s''\<close> have "nullableSym s nu" using Cons.prems(1)
        by (auto simp add: nullableSym_nullable_sym \<open>s'' = s\<close>)
      then show ?thesis using False by auto
    qed
  qed
qed

lemma updateFo_preserves_soundness':
  "nullable_set_for nu g \<Longrightarrow> first_map_for fi g \<Longrightarrow> (lx, gpre @ gsuf) \<in> set (prods g)
  \<Longrightarrow> follow_map_sound fo g \<Longrightarrow> follow_map_sound (updateFo nu fi lx gsuf fo) g"
proof (induction nu fi lx gsuf fo arbitrary: gpre rule: updateFo_induct_refined)
  case (1 nu fi lx fo)
  then show ?case by auto
next
  case (2 nu fi lx y gsuf fo)
  then show ?case by (auto intro: "2.IH"[where gpre = "gpre @ [T y]"])
next
  case (3 nu fi lx rx gsuf fo)
  then show ?case by (auto intro: "3.IH"[where gpre = "gpre @ [NT rx]"])
next
  case (4 nu fi lx rx gsuf fo)
  let ?fo' = "updateFo nu fi lx gsuf fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gsuf nu fi"
  let ?additions = "(if nullableGamma gsuf nu then ?lSet @@ ?rSet else ?rSet)"
  have IH: "follow_map_sound (updateFo nu fi lx gsuf fo) g"
    by (auto intro: "4.IH"[where gpre = "gpre @ [NT rx]"] simp add: "4.prems"(1,2,3,4))
  have simp_updFo: "updateFo nu fi lx (NT rx # gsuf) fo = fmupd rx ?additions ?fo'"
    by (simp add: 4 Let_def)
  have "fmlookup (updateFo nu fi lx (NT rx # gsuf) fo) x = Some xFollow \<and> la \<in> set xFollow
    \<Longrightarrow> follow_sym g la (NT x)" for x xFollow la
  proof (cases "rx = x")
    case True
    assume "fmlookup (updateFo nu fi lx (NT rx # gsuf) fo) x = Some xFollow \<and> la \<in> set xFollow"
      and "rx = x"
    then have "la \<in> set ?additions" using simp_updFo by auto
    then consider (la_in_lSet) "nullableGamma gsuf nu" "la \<in> set ?lSet"
      | (la_in_rSet) "la \<in> set ?rSet" by (auto split: if_splits)
    then show "follow_sym g la (NT x)"
    proof (cases)
      case la_in_lSet
      then obtain lxFollow where "fmlookup ?fo' lx = Some lxFollow" "la \<in> set lxFollow"
        using in_findOrEmpty_exists_set by fast
      then have "follow_sym g la (NT lx)" using follow_map_sound_def IH by fastforce
      moreover have "(lx, gpre @ NT x # gsuf) \<in> set (prods g)" using "4.prems"(3)  \<open>rx = x\<close> by blast
      moreover have "nullable_gamma g gsuf"
        using la_in_lSet "4.prems"(1) nu_sound_nullableGamma_sound by blast
      ultimately show ?thesis by - (rule FollowLeft)
    next
      case la_in_rSet
      then have "first_gamma g la gsuf" using firstGamma_first_gamma "4.prems"(1,2) by fastforce
      moreover have "(lx, gpre @ NT x # gsuf) \<in> set (prods g)" using "4.prems"(3) True by blast
      ultimately show ?thesis by - (rule FollowRight)
    qed
  next
    case False
    assume A: "fmlookup (updateFo nu fi lx (NT rx # gsuf) fo) x = Some xFollow \<and> la \<in> set xFollow"
    then show "follow_sym g la (NT x)" using False IH follow_map_sound_def simp_updFo by fastforce
  qed
  then show ?case using follow_map_sound_def by fast
next
  case (5 nu fi lx rx gsuf fo rxFollow)
  then show ?case by (auto intro: "5.IH"[where gpre = "gpre @ [NT rx]"])
next
  case (6 nu fi lx rx gsuf fo rxFollow)
  let ?fo' = "updateFo nu fi lx gsuf fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gsuf nu fi"
  let ?additions = "(if nullableGamma gsuf nu then ?lSet @@ ?rSet else ?rSet)"
  have IH: "follow_map_sound (updateFo nu fi lx gsuf fo) g"
    by (auto intro: "6.IH"[where gpre = "gpre @ [NT rx]"] simp add: "6.prems"(1,2,3,4))
  have simp_updFo: "updateFo nu fi lx (NT rx # gsuf) fo = fmupd rx (rxFollow @@ ?additions) ?fo'"
    by (simp add: 6 Let_def)
  have "fmlookup (updateFo nu fi lx (NT rx # gsuf) fo) x = Some xFollow \<and> la \<in> set xFollow
          \<Longrightarrow> follow_sym g la (NT x)" for x xFollow la
  proof (cases "rx = x")
    case True
    assume "fmlookup (updateFo nu fi lx (NT rx # gsuf) fo) x = Some xFollow \<and> la \<in> set xFollow"
      and "rx = x"
    then have "la \<in> set rxFollow \<or> la \<in> set ?additions" using simp_updFo by auto
    then consider (la_in_rxFollow) "la \<in> set rxFollow"
      | (la_in_lSet) "nullableGamma gsuf nu" "la \<in> set ?lSet" | (la_in_rSet) "la \<in> set ?rSet"
      by (auto split: if_splits)
    then show "follow_sym g la (NT x)"
    proof (cases)
      case la_in_rxFollow
      then show ?thesis using IH True follow_map_sound_def using "6.hyps"(1) by fastforce
    next
      case la_in_lSet
      then obtain lxFollow where "fmlookup ?fo' lx = Some lxFollow" "la \<in> set lxFollow"
        using in_findOrEmpty_exists_set by fast
      then have "follow_sym g la (NT lx)" using IH follow_map_sound_def by fastforce
      moreover have "(lx, gpre @ NT x # gsuf) \<in> set (prods g)"
        using \<open>rx = x\<close> "6.prems"(3) by auto
      moreover have "nullable_gamma g gsuf"
        using la_in_lSet "6.prems"(1) nu_sound_nullableGamma_sound by auto
      ultimately show ?thesis by - (rule FollowLeft)
    next
      case la_in_rSet
      then have "first_gamma g la gsuf" using firstGamma_first_gamma "6.prems"(1,2) by fastforce
      moreover have "(lx, gpre @ NT x # gsuf) \<in> set (prods g)" using "6.prems"(3) True by auto
      ultimately show ?thesis by - (rule FollowRight)
    qed
  next
    case False
    assume A: "fmlookup (updateFo nu fi lx (NT rx # gsuf) fo) x = Some xFollow \<and> la \<in> set xFollow"
    have "updateFo nu fi lx (NT rx # gsuf) fo = fmupd rx (rxFollow @@ ?additions) ?fo'" by
      (simp add: 6 Let_def)
    then have "fmlookup (updateFo nu fi lx gsuf fo) x = Some xFollow" using A by
      (auto simp add: False)
    then show "follow_sym g la (NT x)" using IH A(1) unfolding follow_map_sound_def by blast
  qed
  then show ?case unfolding follow_map_sound_def by blast
qed

lemma updateFo_preserves_soundness: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> (lx, gamma) \<in> set (prods g) \<Longrightarrow> follow_map_sound fo g
  \<Longrightarrow> follow_map_sound (updateFo nu fi lx gamma fo) g"
  by (metis self_append_conv2 updateFo_preserves_soundness')

lemma followPass_preserves_soundness': "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> follow_map_sound fo g \<Longrightarrow> pre @ suf = prods g
  \<Longrightarrow> follow_map_sound (followPass suf nu fi fo) g"
proof (induction suf arbitrary: pre)
  case Nil
  then show ?case by (simp add: followPass_def)
next
  case (Cons p suf)
  obtain lx gamma where "p = (lx, gamma)" by fastforce
  have "follow_map_sound (updateFo nu fi lx gamma (followPass suf nu fi fo)) g"
  proof (rule updateFo_preserves_soundness)
    show "(lx, gamma) \<in> set (prods g)" using Cons.prems(4)
      by (metis \<open>p = (lx, gamma)\<close> in_set_conv_decomp)
  next
    have "(pre @ [p]) @ suf = prods g" using Cons.prems(4) by auto
    then show "follow_map_sound (followPass suf nu fi fo) g"
      using Cons.prems(1,2,3) by - (rule Cons.IH[where pre = "pre @ [p]"])
  qed (auto simp add: Cons.prems(1,2))
  then show ?case by (simp add: \<open>p = (lx, gamma)\<close>)
qed

lemma followPass_preserves_soundness: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> follow_map_sound fo g \<Longrightarrow> follow_map_sound (followPass (prods g) nu fi fo) g"
  by (simp add: followPass_preserves_soundness')

lemma mkFollowMap'_preserves_soundness: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> follow_map_sound fo g \<Longrightarrow> all_pairs_are_follow_candidates fo g
  \<Longrightarrow> follow_map_sound (the (mkFollowMap' g nu fi fo)) g"
proof (induction "countFollowCands g fo" arbitrary: fo rule: less_induct)
  case less
  let ?fo' = "followPass (prods g) nu fi fo"
  have "mkFollowMap' g nu fi fo \<noteq> None" by (simp add: less.prems(2,4) mkFollowMap'_dom_if_apac)
  moreover have "follow_map_sound (if fo = ?fo' then fo else the (mkFollowMap' g nu fi ?fo')) g"
  proof (cases "fo = ?fo'")
    case True
    then show ?thesis using less.prems(3) by auto
  next
    case False
    have "countFollowCands g ?fo' < countFollowCands g fo"
      by (simp add: False followPass_not_equiv_candidates_lt less.prems(2,4))
    moreover have "follow_map_sound ?fo' g"
      using less.prems by - (rule followPass_preserves_soundness, auto)
    ultimately show ?thesis using followPass_preserves_apac less by fastforce
  qed
  ultimately show ?case using mkFollowMap'.simps[of g nu fi fo] by (auto simp add: Let_def)
qed

lemma initial_fo_sound: "follow_map_sound (initial_fo g) g"
  unfolding follow_map_sound_def using FollowStart by auto

theorem mkFollowMap_sound:
  "nullable_set_for nu g \<Longrightarrow> first_map_for fi g \<Longrightarrow> follow_map_sound (mkFollowMap g nu fi) g"
  unfolding mkFollowMap_def
  by (simp add: initial_fo_apac initial_fo_sound mkFollowMap'_preserves_soundness)


subsection \<open>Completeness\<close>

lemma updateFo_preserves_map_keys: "x |\<in>| fmdom fo \<Longrightarrow> x |\<in>| fmdom (updateFo nu fi lx gamma fo)"
  by (induction nu fi lx gamma fo rule: updateFo_induct_refined) (auto simp add: Let_def)

lemma followPass_preserves_map_keys: "x |\<in>| fmdom fo \<Longrightarrow> x |\<in>| fmdom (followPass ps nu fi fo)"
proof (induction ps)
  case Nil
  then show ?case by (simp add: followPass_def)
next
  case (Cons p ps)
  obtain x gamma where "p = (x, gamma)" by fastforce
  then show ?case by (simp add: updateFo_preserves_map_keys Cons)
qed

lemma find_updateFo_cons_neq: "x \<noteq> x' \<Longrightarrow> fmlookup (updateFo nu fi lx gsuf fo) x = Some xFollow
  \<longleftrightarrow> fmlookup (updateFo nu fi lx (NT x' # gsuf) fo) x = Some xFollow"
proof -
  assume "x \<noteq> x'"
  let ?fo' = "updateFo nu fi lx gsuf fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gsuf nu fi"
  let ?additions = "(if nullableGamma gsuf nu then ?lSet @@ ?rSet else ?rSet)"
  show "(fmlookup ?fo' x = Some xFollow) =
    (fmlookup (updateFo nu fi lx (NT x' # gsuf) fo) x = Some xFollow)"
  proof (cases "fmlookup (updateFo nu fi lx gsuf fo) x'")
    case None
    show ?thesis
    proof (cases "?additions = []")
      case True
      show ?thesis by (auto simp add: True None)
    next
      case False
      have "fmlookup (updateFo nu fi lx (NT x' # gsuf) fo) x =
        fmlookup (updateFo nu fi lx gsuf fo) x" using \<open>x \<noteq> x'\<close>
        by (auto simp add: Let_def False None)
      then show ?thesis by auto
    qed
  next
    case (Some rxFollow)
    then show ?thesis
    proof (cases "set ?additions \<subseteq> set rxFollow")
      case True
      show ?thesis by (auto simp add: True Some)
    next
      case False
      have "fmlookup (updateFo nu fi lx (NT x' # gsuf) fo) x =
        fmlookup (updateFo nu fi lx gsuf fo) x" using \<open>x \<noteq> x'\<close>
        by (auto simp add: Let_def False Some)
      then show ?thesis by auto
    qed
  qed
qed

lemma updateFo_value_subset:
  "fmlookup fo x = Some s1 \<Longrightarrow> fmlookup (updateFo nu fi lx gamma fo) x = Some s2
  \<Longrightarrow> set s1 \<subseteq> set s2"
proof (induction nu fi lx gamma fo arbitrary: s2 rule: updateFo_induct_refined)
  case (4 nu fi lx rx gamma' fo)
  show ?case
  proof (cases "x = rx")
    case True
    from "4.prems"(1) have "x |\<in>| fmdom fo" by (simp add: fmdomI)
    then have "x |\<in>| fmdom (updateFo nu fi lx gamma' fo)" by
      (auto intro: updateFo_preserves_map_keys)
    moreover have "x |\<notin>| fmdom (updateFo nu fi lx gamma' fo)" using "4.hyps"(1) by
      (simp add: True fmdom_notI)
    ultimately have "False" by auto
    then show ?thesis by auto
  next
    case False
    with "4.prems"(2) have "fmlookup (updateFo nu fi lx gamma' fo) x = Some s2" by
      (auto simp add: Let_def "4.hyps")
    then show ?thesis using "4.IH" "4.prems"(1) by auto
  qed
next
  case (6 nu fi lx rx gamma' fo rxFollow)
  then show ?case
  proof (cases "x = rx")
    case True
    let ?fo' = "updateFo nu fi lx gamma' fo"
    let ?lSet = "findOrEmpty lx ?fo'"
    let ?rSet = "firstGamma gamma' nu fi"
    let ?additions = "(if nullableGamma gamma' nu then ?lSet @@ ?rSet else ?rSet)"
    from "6.prems"(2) have "set s2 = set (?additions @@ rxFollow)"
      by (auto simp add: Let_def "6.hyps" True)
    moreover have "set s1 \<subseteq> set rxFollow" using "6.IH" "6.hyps"(1) "6.prems"(1) True by blast
    ultimately show ?thesis by auto
  next
    case False
    with "6.prems"(2) have "fmlookup (updateFo nu fi lx gamma' fo) x = Some s2" by
      (auto simp add: Let_def "6.hyps")
    then show ?thesis using "6.IH" "6.prems"(1) by auto
  qed
qed auto

lemma updateFo_only_appends:
  "fmlookup fo x = Some s1 \<Longrightarrow> fmlookup (updateFo nu fi lx gamma fo) x = Some s2
  \<Longrightarrow> \<exists>suf. s2 = s1 @ suf"
proof (induction nu fi lx gamma fo arbitrary: s2 rule: updateFo_induct_refined)
  case (4 nu fi lx rx gamma' fo)
  then show ?case
  proof (cases "x = rx")
    case True
    have "x |\<in>| fmdom fo" by (simp add: "4.prems"(1) fmdomI)
    then have "x |\<in>| fmdom (updateFo nu fi lx gamma' fo)" by (simp add: updateFo_preserves_map_keys)
    then have "False" using "4.hyps"(1) by (simp add: True fmdom_notI)
    then show ?thesis by auto
  next
    case False
    have "fmlookup (updateFo nu fi lx gamma' fo) x = Some s2"
      using "4.prems"(2) False find_updateFo_cons_neq by fast
    then show ?thesis using "4.IH" "4.prems"(1) by auto
  qed
next
  case (6 nu fi lx rx gamma' fo rxFollow)
  let ?fo' = "updateFo nu fi lx gamma' fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gamma' nu fi"
  let ?additions = "(if nullableGamma gamma' nu then ?lSet @@ ?rSet else ?rSet)"
  have "updateFo nu fi lx (NT rx # gamma') fo = (case fmlookup ?fo' rx of
      None \<Rightarrow> (if ?additions = [] then ?fo' else fmupd rx ?additions ?fo')
    | Some rxFollow \<Rightarrow> (if set ?additions \<subseteq> set rxFollow then ?fo'
        else fmupd rx (rxFollow @@ ?additions) ?fo'))"
    by (metis updateFo.simps(3))
  then have A: "updateFo nu fi lx (NT rx # gamma') fo = fmupd rx (rxFollow @@ ?additions) ?fo'"
    by (simp add: "6.hyps"(1) "6.hyps"(2))
  show ?case
  proof (cases "x = rx")
    case True
    then show ?thesis
      using "6.IH"[OF "6.prems"(1)] "6.hyps"(1) "6.prems"(2) A unfolding list_union_def by auto
  next
    case False
    then show ?thesis by (meson "6.IH" "6.prems"(1) "6.prems"(2) find_updateFo_cons_neq)
  qed
qed auto


lemma followPass_value_subset:
  "fmlookup fo x = Some s1 \<Longrightarrow> fmlookup (followPass ps nu fi fo) x = Some s2 \<Longrightarrow> set s1 \<subseteq> set s2"
proof (induction ps arbitrary: s1 s2)
  case Nil
  then show ?case by (simp add: followPass_def)
next
  case (Cons p ps)
  obtain y gamma where "p = (y, gamma)" by fastforce
  have "x |\<in>| fmdom (followPass ps nu fi fo)" by
    (simp add: Cons.prems(1) fmdomI followPass_preserves_map_keys)
  then obtain s where s_def: "fmlookup (followPass ps nu fi fo) x = Some s" by
    (auto simp add: fmdomI)
  then have s1_subset_s: "set s1 \<subseteq> set s" using Cons.prems(1) Cons.IH by auto
  have "fmlookup (updateFo nu fi y gamma (followPass ps nu fi fo)) x = Some s2" using Cons.prems(2)
    by (simp add: \<open>p = (y, gamma)\<close>)
  then have s_subset_s2: "set s \<subseteq> set s2" using s_def by
    - (rule updateFo_value_subset[where ?fo = "followPass ps nu fi fo"])
  show ?case using s1_subset_s s_subset_s2 by auto
qed

lemma followPass_only_appends: "fmlookup fo x = Some s1
  \<Longrightarrow> fmlookup (followPass ps nu fi fo) x = Some s2 \<Longrightarrow> \<exists>suf. s2 = s1 @ suf"
proof (induction ps arbitrary: s1 s2)
  case Nil
  then show ?case by (simp add: followPass_def)
next
  case (Cons p ps)
  obtain y gamma where "p = (y, gamma)" by fastforce
  have "x |\<in>| fmdom (followPass ps nu fi fo)" by
    (simp add: Cons.prems(1) fmdomI followPass_preserves_map_keys)
  then obtain s where s_def: "fmlookup (followPass ps nu fi fo) x = Some s" by
    (auto simp add: fmdomI)
  moreover obtain suf where "s = s1 @ suf" using Cons.prems(1) Cons.IH s_def by auto
  moreover have "fmlookup (updateFo nu fi y gamma (followPass ps nu fi fo)) x = Some s2"
    using Cons.prems(2) by (simp add: \<open>p = (y, gamma)\<close>)
  ultimately show ?case using updateFo_only_appends[OF s_def] by fastforce
qed

lemma followPass_equiv_cons_tl: "fo = followPass ((x, gamma) # ps) nu fi fo
  \<Longrightarrow> fo = followPass ps nu fi fo"
proof (rule fmap_ext)
  fix y
  assume assm: "fo = followPass ((x, gamma) # ps) nu fi fo"
  then show "fmlookup fo y = fmlookup (followPass ps nu fi fo) y"
  proof (cases "fmlookup fo y")
    case None
    then have "y |\<notin>| fmdom (followPass ((x, gamma) # ps) nu fi fo)" using assm by auto
    then have "y |\<notin>| fmdom (followPass ps nu fi fo)" by (auto intro: updateFo_preserves_map_keys)
    then show ?thesis using None by auto
  next
    case (Some yFollow)
    then have "y |\<in>| fmdom (followPass ps nu fi fo)" by
        (simp add: fmdomI followPass_preserves_map_keys)
    then obtain yFollow' where yFollow'_def: "fmlookup (followPass ps nu fi fo) y = Some yFollow'"
      by auto
    from assm have "fmlookup (updateFo nu fi x gamma (followPass ps nu fi fo)) y = Some yFollow" by
        (simp add: Some)
    then have "\<exists>suf. yFollow = yFollow' @ suf" using updateFo_only_appends[OF yFollow'_def] by fast
    moreover have "\<exists>suf. yFollow' = yFollow @ suf"
      using followPass_only_appends[OF Some yFollow'_def] by auto
    ultimately show ?thesis using Some yFollow'_def by fastforce
  qed
qed

lemma exists_follow_set_Cons:
  assumes "nullable_set_for nu g" "first_map_for fi g"
  and "\<exists>rxFollow. fmlookup (updateFo nu fi lx gamma fo) rx = Some rxFollow
    \<and> la \<in> set rxFollow"
  shows "\<exists>rxFollow. fmlookup (updateFo nu fi lx (s # gamma) fo) rx = Some rxFollow
    \<and> la \<in> set rxFollow"
proof (cases s)
  case (NT rx')
  then show ?thesis
  proof (cases "rx = rx'")
    case True
    let ?fo' = "updateFo nu fi lx gamma fo"
    let ?lSet = "findOrEmpty lx ?fo'"
    let ?rSet = "firstGamma gamma nu fi"
    let ?additions = "(if nullableGamma gamma nu then ?lSet @@ ?rSet else ?rSet)"
    obtain rxFollow where rxFollow_def: "fmlookup ?fo' rx = Some rxFollow" "la \<in> set rxFollow"
      using assms(3) by auto
    then have "fmlookup ?fo' rx' = Some rxFollow" using True by auto
    then show ?thesis
    proof (cases "set ?additions \<subseteq> set rxFollow")
      case True
      then show ?thesis by (simp add: NT \<open>fmlookup ?fo' rx' = Some rxFollow\<close> True rxFollow_def)
    next
      case False
      have "updateFo nu fi lx (NT rx' # gamma) fo =
        fmupd rx' (rxFollow @@ ?additions) ?fo'"
        by (simp add: NT \<open>fmlookup ?fo' rx' = Some rxFollow\<close> False Let_def)
      then have "fmlookup (updateFo nu fi lx (s # gamma) fo) rx =
        Some (rxFollow @@ ?additions)" by (simp add: NT True)
      moreover have "la \<in> set (rxFollow @@ ?additions)" using rxFollow_def(2) by auto
      ultimately show ?thesis by auto
    qed
  next
    case False
    then show ?thesis using find_updateFo_cons_neq NT assms(3) by fastforce
  qed
next
  case (T y)
  then show ?thesis by (simp add: assms)
qed

lemma exists_follow_set_containing_first_gamma:
  "nullable_set_for nu g \<Longrightarrow> first_map_for fi g \<Longrightarrow> first_gamma g la gsuf
  \<Longrightarrow> (\<exists>rxFollow. fmlookup (updateFo nu fi lx (gpre @ NT rx # gsuf) fo) rx = Some rxFollow
    \<and> la \<in> set rxFollow)"
proof (induction gpre)
  case Nil
  let ?fo' = "updateFo nu fi lx gsuf fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gsuf nu fi"
  let ?additions = "(if nullableGamma gsuf nu then ?lSet @@ ?rSet else ?rSet)"
  show ?case
  proof (cases "fmlookup (updateFo nu fi lx gsuf fo) rx")
    case None
    then show ?thesis
    proof (cases "?additions = []")
      case True
      then show ?thesis
        by (metis Nil.prems UnI2 empty_iff first_gamma_firstGamma list.set(1) set_list_union)
    next
      case False
      have "la \<in> set (firstGamma gsuf nu fi)" using Nil first_gamma_firstGamma by blast
      then have "la \<in> set ?additions" by auto
      moreover have "fmlookup (updateFo nu fi lx ([] @ NT rx # gsuf) fo) rx = Some ?additions" by
        (simp add: None False Let_def)
      ultimately show ?thesis by auto
    qed
  next
    case (Some rxFollow)
    then show ?thesis
    proof (cases "set ?additions \<subseteq> set rxFollow")
      case True
      then show ?thesis
        using Nil Some first_gamma_firstGamma by fastforce
    next
      case False
      have "la \<in> set (firstGamma gsuf nu fi)" using Nil first_gamma_firstGamma by blast
      then have "la \<in> set (rxFollow @@ ?additions)" by auto
      moreover have "fmlookup (updateFo nu fi lx ([] @ NT rx # gsuf) fo) rx =
        Some (rxFollow @@ ?additions)" by (simp add: Some False Let_def)
      ultimately show ?thesis by auto
    qed
  qed
next
  case (Cons s gpre)
  then show ?case using exists_follow_set_Cons by fastforce
qed

lemma followPass_equiv_right: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> fo = followPass psuf nu fi fo \<Longrightarrow> (lx, gpre @ NT rx # gsuf) \<in> set psuf
  \<Longrightarrow> first_gamma g la gsuf \<Longrightarrow> ppre @ psuf = prods g
  \<Longrightarrow> (\<exists>rxFollow. fmlookup fo rx = Some rxFollow \<and> la \<in> set rxFollow)"
proof (induction psuf arbitrary: ppre)
  case Nil
  then show ?case  by auto
next
  case (Cons p ps)
  obtain x gamma where "p = (x, gamma)" by fastforce
  from Cons.prems(4) have "(lx, gpre @ NT rx # gsuf) \<in> set (p # ps)" by auto
  then consider (is_p) "(lx, gpre @ NT rx # gsuf) = (x, gamma)"
    | (in_ps) "(lx, gpre @ NT rx # gsuf) \<in> set ps" using \<open>p = (x, gamma)\<close> by auto
  then show ?case
  proof cases
    case is_p
    have "\<exists>rxFollow. fmlookup (updateFo nu fi lx (gpre @ NT rx # gsuf) (followPass ps nu fi fo)) rx
      = Some rxFollow \<and> la \<in> set rxFollow" using Cons.prems(1,2,5)
      by (rule exists_follow_set_containing_first_gamma)
    then show ?thesis
      using Cons.prems(3) \<open>p = (x, gamma)\<close> is_p by auto
  next
    case in_ps
    have "fo = followPass ps nu fi fo" using Cons.prems(3) \<open>p = (x, gamma)\<close> by
      - (rule followPass_equiv_cons_tl, auto)
    moreover have "(ppre @ [p]) @ ps = prods g" by (simp add: Cons.prems(6))
    ultimately show ?thesis using Cons.IH Cons.prems(1,2,5) in_ps by fastforce
  qed
qed

lemma nullable_gamma_nullableGamma:
  "nullable_set_for nu g \<Longrightarrow> nullable_gamma g gamma \<Longrightarrow> nullableGamma gamma nu"
proof (induction gamma)
  case Nil
  then show ?case by auto
next
  case (Cons s gamma)
  from Cons.prems(2) have "nullable_gamma g gamma" "nullable_sym g s" by
    (auto elim: nullable_gamma.cases)
  from \<open>nullable_sym g s\<close> obtain x where "s = NT x" by (auto intro: nullable_sym.cases)
  then have "x \<in> nu" using \<open>nullable_sym g s\<close> Cons.prems(1) unfolding nullable_set_complete_def by
    auto
  moreover have "nullableGamma gamma nu" using \<open>nullable_gamma g gamma\<close> by
    (auto intro: Cons.IH simp add: Cons.prems(1))
  ultimately show ?case by (simp add: \<open>s = NT x\<close>)
qed

lemma updateFo_preserves_membership_in_value:
  "fmlookup fo x = Some s \<Longrightarrow> la \<in> set s \<Longrightarrow> la \<in> set (findOrEmpty x (updateFo nu fi x' gamma fo))"
proof -
  assume A: "fmlookup fo x = Some s" "la \<in> set s"
  then have "x |\<in>| fmdom fo" by (simp add: fmdomI)
  then have "x |\<in>| fmdom (updateFo nu fi x' gamma fo)" by (simp add: updateFo_preserves_map_keys)
  then obtain s' where s'_def: "fmlookup (updateFo nu fi x' gamma fo) x = Some s'" by auto
  then have "set s \<subseteq> set s'" using A by - (rule updateFo_value_subset)
  then show ?thesis unfolding findOrEmpty_def using A(2) s'_def by auto
qed

lemma exists_follow_set_containing_follow_left: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> nullable_gamma g gsuf \<Longrightarrow> fmlookup fo lx = Some lxFollow \<Longrightarrow> la \<in> set lxFollow
  \<Longrightarrow> (\<exists>rxFollow. fmlookup (updateFo nu fi lx (gpre @ NT rx # gsuf) fo) rx = Some rxFollow
  \<and> la \<in> set rxFollow)"
proof (induction gpre)
  case Nil
  let ?fo' = "updateFo nu fi lx gsuf fo"
  let ?lSet = "findOrEmpty lx ?fo'"
  let ?rSet = "firstGamma gsuf nu fi"
  let ?additions = "(if nullableGamma gsuf nu then ?lSet @@ ?rSet else ?rSet)"
  have "nullableGamma gsuf nu" using Nil.prems(1,3) nullable_gamma_nullableGamma by auto
  then have "?additions = ?lSet @@ ?rSet" by auto
  show ?case
  proof (cases "fmlookup (updateFo nu fi lx gsuf fo) rx")
    case None
    show ?thesis
    proof (cases "?additions = []")
      case True
      then show ?thesis
        using Nil.prems(1,3-5) nullable_gamma_nullableGamma updateFo_preserves_membership_in_value
        by (metis Nil_is_append_conv emptyE empty_set list_union_def)
    next
      case False
      have "la \<in> set (?lSet @@ ?rSet)" by
        (simp add: Nil.prems(4,5) updateFo_preserves_membership_in_value)
      moreover have "updateFo nu fi lx (NT rx # gsuf) fo =
        fmupd rx ?additions (updateFo nu fi lx gsuf fo)" by (simp add: None False Let_def)
      ultimately show ?thesis using \<open>?additions = ?lSet @@ ?rSet\<close> by simp
    qed
  next
    case (Some rxFollow)
    show ?thesis
    proof (cases "set ?additions \<subseteq> set rxFollow")
      case True
      then show ?thesis
        using Nil.prems(4,5) Some \<open>nullableGamma gsuf nu\<close> updateFo_preserves_membership_in_value
        by fastforce
    next
      case False
      have "la \<in> set (?lSet @@ ?rSet)" by
          (simp add: Nil.prems(4,5) updateFo_preserves_membership_in_value)
      moreover have "updateFo nu fi lx (NT rx # gsuf) fo =
        fmupd rx (rxFollow @@ ?additions) (updateFo nu fi lx gsuf fo)"
        by (simp add: Some False Let_def)
      ultimately show ?thesis using \<open>?additions = ?lSet @@ ?rSet\<close> by simp
    qed
  qed
next
  case (Cons s gpre)
  then show ?case using exists_follow_set_Cons by fastforce
qed

lemma followPass_equiv_left: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> fo = followPass psuf nu fi fo \<Longrightarrow> (lx, gpre @ NT rx # gsuf) \<in> set psuf
  \<Longrightarrow> ppre @ psuf = prods g \<Longrightarrow> nullable_gamma g gsuf \<Longrightarrow> fmlookup fo lx = Some lxFollow
  \<Longrightarrow> la \<in> set lxFollow \<Longrightarrow> (\<exists>rxFollow. fmlookup fo rx = Some rxFollow \<and> la \<in> set rxFollow)"
proof (induction psuf arbitrary: ppre)
  case Nil
  then show ?case  by auto
next
  case (Cons p ps)
  let ?fo' = "followPass ps nu fi fo"
  obtain x gamma where "p = (x, gamma)" by fastforce
  from Cons.prems(4) consider (is_p) "(lx, gpre @ NT rx # gsuf) = (x, gamma)"
    | (in_ps) "(lx, gpre @ NT rx # gsuf) \<in> set ps" using \<open>p = (x, gamma)\<close> by auto
  then show ?case
  proof cases
    case is_p
    have "fmlookup ?fo' lx = Some lxFollow"
      using Cons.prems(3,7) \<open>p = (x, gamma)\<close> followPass_equiv_cons_tl by fastforce
    then have "\<exists>rxFollow. fmlookup (updateFo nu fi lx (gpre @ NT rx # gsuf) ?fo') rx =
      Some rxFollow \<and> la \<in> set rxFollow" using Cons.prems(1,2,6,8)
      by - (rule exists_follow_set_containing_follow_left)
    then show ?thesis using Cons.prems(3) \<open>p = (x, gamma)\<close> is_p by auto
  next
    case in_ps
    have "fo = ?fo'" using Cons.prems(3) \<open>p = (x, gamma)\<close> by - (rule followPass_equiv_cons_tl, auto)
    moreover have "(ppre @ [p]) @ ps = prods g" by (simp add: Cons.prems(5))
    ultimately show ?thesis using Cons.IH Cons.prems(1,2,6,7,8) in_ps by fastforce
  qed
qed

lemma followPass_equiv_complete: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> (start g, EOF) \<in> pairsOf fo \<Longrightarrow> fo = followPass (prods g) nu fi fo
  \<Longrightarrow> follow_map_complete fo g"
proof -
  assume A: "nullable_set_for nu g" "first_map_for fi g"
    "(start g, EOF) \<in> pairsOf fo" "fo = followPass (prods g) nu fi fo"
  have "follow_sym g la s
    \<Longrightarrow> (\<forall>x. s = NT x \<longrightarrow> (\<exists>xFollow. fmlookup fo x = Some xFollow \<and> la \<in> set xFollow))" for la s
  proof -
    assume "follow_sym g la s"
    then show "(\<forall>x. s = NT x \<longrightarrow> (\<exists>xFollow. fmlookup fo x = Some xFollow \<and> la \<in> set xFollow))"
    proof (induction rule: follow_sym.induct)
      case FollowStart
      show ?case by (simp add: A(3) in_pairsOf_exists[symmetric])
    next
      case (FollowRight x1 gpre x2 gsuf la)
      then show ?case using A followPass_equiv_right by fast
    next
      case (FollowLeft x1 gpre x2 gsuf la)
      then show ?case using A followPass_equiv_left by fast
    qed
  qed
  then show ?thesis unfolding follow_map_complete_def by auto
qed

lemma mkFollowMap'_complete: "(start g, EOF) \<in> pairsOf fo \<Longrightarrow> nullable_set_for nu g
  \<Longrightarrow> first_map_for fi g \<Longrightarrow> all_pairs_are_follow_candidates fo g
  \<Longrightarrow> follow_map_complete (the (mkFollowMap' g nu fi fo)) g"
proof (induction "countFollowCands g fo" arbitrary: fo rule: less_induct)
  case less
  let ?fo' = "followPass (prods g) nu fi fo"
  have "mkFollowMap' g nu fi fo \<noteq> None" by (simp add: less.prems(3,4) mkFollowMap'_dom_if_apac)
  moreover have "follow_map_complete (if fo = ?fo' then fo else the (mkFollowMap' g nu fi ?fo')) g"
  proof (cases "fo = ?fo'")
    case True
    then show ?thesis using followPass_equiv_complete less.prems(1,2,3) by auto
  next
    case False
    have "countFollowCands g ?fo' < countFollowCands g fo" by
      (simp add: False followPass_not_equiv_candidates_lt less.prems(3,4))
    moreover have "(start g, EOF) \<in> pairsOf ?fo'" using followPass_subset less.prems(1) by blast
    moreover have "all_pairs_are_follow_candidates ?fo' g" by
      (simp add: followPass_preserves_apac less.prems(3,4))
    ultimately show ?thesis by (auto intro: less.hyps simp add: False less.prems(2,3))
  qed
  ultimately show ?case using mkFollowMap'.simps[of g nu fi fo] by (auto simp add: Let_def)
qed

lemma start_eof_in_initial_fo: "(start g, EOF) \<in> pairsOf (initial_fo g)"
  by (simp add: in_add_value)

theorem mkFollowMap_complete:
  "nullable_set_for nu g \<Longrightarrow> first_map_for fi g \<Longrightarrow> follow_map_complete (mkFollowMap g nu fi) g"
  by (simp add: initial_fo_apac mkFollowMap'_complete mkFollowMap_def start_eof_in_initial_fo)

theorem mkFollowMap_correct:
  "nullable_set_for nu g \<Longrightarrow> first_map_for fi g \<Longrightarrow> follow_map_for (mkFollowMap g nu fi) g"
  by (simp add: mkFollowMap_complete mkFollowMap_sound)

declare mkFollowMap'.simps[code]

end