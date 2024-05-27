section \<open>Parse Table\<close>

theory Parse_Table
imports Follow_Map
begin

text\<open>From the (correct) NULLABLE, FIRST, and FOLLOW sets we build a list of parse table entries.\<close>

type_synonym ('n, 't) table_key = "('n \<times> 't lookahead)"

type_synonym ('n, 't) parse_table = "(('n \<times> 't lookahead), ('n, 't) prod) fmap"


definition firstKeysForProd ::
  "('n, 't) prod \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map \<Rightarrow> ('n, 't) table_key list" where
  "firstKeysForProd \<equiv> (\<lambda>(x, gamma) nu fi. map (\<lambda>la. (x, la)) (firstGamma gamma nu fi))"

definition followKeysForProd :: "('n, 't) prod \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map
    \<Rightarrow> ('n, 't) follow_map \<Rightarrow> ('n, 't) table_key list" where
  "followKeysForProd \<equiv> (\<lambda>(x, gamma) nu fi fo.
    map (\<lambda>la. (x, la)) (if nullableGamma gamma nu then findOrEmpty x fo else []))"

abbreviation keysForProd :: "'n set \<Rightarrow> ('n, 't) first_map \<Rightarrow> ('n, 't) follow_map \<Rightarrow> ('n, 't) prod
    \<Rightarrow> ('n, 't) table_key list" where
  "keysForProd nu fi fo xp \<equiv> (firstKeysForProd xp nu fi) @ (followKeysForProd xp nu fi fo)"

datatype ('n, 't) ll1_parse_table = PT "('n, 't) parse_table"
  | ERROR_GRAMMAR_NOT_LL1_AMB_LA "'t lookahead \<times> ('n, 't) prod \<times> ('n, 't) prod"

fun addEntries :: "('n \<times> 't lookahead) list \<Rightarrow> ('n, 't) prod \<Rightarrow> ('n, 't) ll1_parse_table
  \<Rightarrow> ('n, 't) ll1_parse_table" where
  "addEntries (k # keys) xp (PT pt) = (case fmlookup pt k of
      None \<Rightarrow> addEntries keys xp (PT (fmupd k xp pt))
    | Some xp' \<Rightarrow> (if xp = xp' then addEntries keys xp (PT pt)
        else ERROR_GRAMMAR_NOT_LL1_AMB_LA (snd k, xp, xp')))"
| "addEntries keys xp pt = pt"

fun mkParseTable' :: "('n, 't) prods \<Rightarrow> 'n set \<Rightarrow> ('n, 't) first_map \<Rightarrow> ('n, 't) follow_map
  \<Rightarrow> ('n, 't) ll1_parse_table \<Rightarrow> ('n, 't) ll1_parse_table" where
  "mkParseTable' [] nu fi fo pt = pt"
| "mkParseTable' (p # ps) nu fi fo pt = (let las = keysForProd nu fi fo p in
    mkParseTable' ps nu fi fo (addEntries las p pt))"

definition mkParseTable :: "('n, 't) grammar \<Rightarrow> ('n, 't) ll1_parse_table" where
  "mkParseTable g = (let
    nu = mkNullableSet g;
    fi = mkFirstMap g nu;
    fo = mkFollowMap g nu fi
  in mkParseTable' (prods g) nu fi fo (PT fmempty))"


subsection \<open>Correctness Definitions\<close>

definition pt_sound :: "('n, 't) parse_table \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "pt_sound pt g \<equiv> (\<forall>x x' la gamma. fmlookup pt (x', la) = Some (x, gamma)
  \<longrightarrow> x' = x \<and> (x, gamma) \<in> set (prods g) \<and> lookahead_for la x gamma g)"

definition pt_complete :: "('n, 't) parse_table \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "pt_complete pt g \<equiv> (\<forall>x la gamma. (x, gamma) \<in> set (prods g) \<and> lookahead_for la x gamma g
  \<longrightarrow> fmlookup pt (x, la) = Some (x, gamma))"

abbreviation parse_table_correct  :: "('n, 't) parse_table \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "parse_table_correct pt g \<equiv> pt_sound pt g \<and> pt_complete pt g"


subsection \<open>Soundness\<close>

lemma firstKeysForProd_lookaheads:
  assumes "nullable_set_for nu g" "first_map_for fi g" "follow_map_for fo g"
    "(x, la) \<in> set (firstKeysForProd (y, gamma) nu fi)"
  shows "x = y \<and> lookahead_for la x gamma g"
  using assms firstGamma_first_gamma unfolding firstKeysForProd_def lookahead_for_def by fastforce

lemma followKeysForProd_lookaheads:
  assumes "nullable_set_for nu g" "first_map_for fi g" "follow_map_for fo g"
    "(x, la) \<in> set (followKeysForProd (y, gamma) nu fi fo)"
  shows "x = y \<and> lookahead_for la x gamma g"
proof (cases "nullableGamma gamma nu")
  case True
  with assms(4) have "la \<in> set (findOrEmpty x fo)" by (auto simp add: followKeysForProd_def)
  then have "follow_sym g la (NT x)" using assms(3) follow_map_sound_def in_findOrEmpty_exists_set
    by fast
  then have "nullable_gamma g gamma \<and> follow_sym g la (NT x)"
    using True assms(1) nu_sound_nullableGamma_sound by blast
  moreover have "x = y" using assms(4) by (auto simp add: followKeysForProd_def)
  ultimately show ?thesis by (simp add: lookahead_for_def)
next
  case False
  then show ?thesis using assms unfolding followKeysForProd_def lookahead_for_def by simp
qed

lemma keys_are_lookaheads:
  assumes "nullable_set_for nu g" "first_map_for fi g" "follow_map_for fo g"
    "(x, la) \<in> set (keysForProd nu fi fo (y, gamma))"
  shows "x = y \<and> lookahead_for la y gamma g"
  using assms firstKeysForProd_lookaheads followKeysForProd_lookaheads
  by fastforce

lemma findOrEmpty_sset_laOf_fi: "first_map_for fi g \<Longrightarrow> set (findOrEmpty x fi) \<subseteq> lookaheadsOf g"
proof
  fix y
  assume A: "first_map_for fi g" "y \<in> set (findOrEmpty x fi)"
  then obtain s where "fmlookup fi x = Some s" "y \<in> set s" using in_findOrEmpty_exists_set by
      fastforce
  then show "y \<in> lookaheadsOf g" using A by (auto intro: first_map_la_in_lookaheadsOf)
qed

lemma follow_sym_in_lookaheadsOf:
  "follow_sym g la (NT x) \<Longrightarrow> la \<in> lookaheadsOf g"
proof (induction rule: follow_sym.induct)
  case (FollowRight x1 gpre x2 gsuf la)
  have "la \<in> lookaheadsOf g"
    using FollowRight.hyps mkFirstMap_correct mkNullableSet_correct
    by - (rule in_firstGamma_in_lookaheadsOf[where ?gpre="gpre @ [NT x2]"],
      auto intro: first_gamma_firstGamma)
  then show ?case unfolding lookaheadsOf_def by auto
qed (simp add: lookaheadsOf_def)

lemma follow_map_la_in_lookaheadsOf:
  "follow_map_for fo g \<Longrightarrow> fmlookup fo x = Some s \<Longrightarrow> la \<in> set s \<Longrightarrow> la \<in> lookaheadsOf g"
  unfolding follow_map_sound_def using follow_sym_in_lookaheadsOf by fastforce

lemma findOrEmpty_sset_laOf_fo: "follow_map_for fo g \<Longrightarrow> set (findOrEmpty x fo) \<subseteq> lookaheadsOf g"
proof
  fix y
  assume A: "follow_map_for fo g" "y \<in> set (findOrEmpty x fo)"
  then obtain s where "fmlookup fo x = Some s" "y \<in> set s" using in_findOrEmpty_exists_set by
      fastforce
  then show "y \<in> lookaheadsOf g" using A by (auto intro: follow_map_la_in_lookaheadsOf)
qed

lemma addEntries_preserves_soundness:
  assumes "nullable_set_for nu g" "first_map_for fi g" "follow_map_for fo g" "p \<in> set (prods g)"
  shows "pt_sound pt g \<Longrightarrow> set las \<subseteq> set (keysForProd nu fi fo p)
    \<Longrightarrow> addEntries las p (PT pt) = PT pt' \<Longrightarrow> pt_sound pt' g"
proof (induction las arbitrary: pt pt')
  case Nil
  then show ?case by auto
next
  case (Cons k las)
  consider (lookup_pt_None) "fmlookup pt k = None"
    | (lookup_pt_Same) "fmlookup pt k = Some p" using Cons.prems(3) by fastforce
  then show ?case
  proof cases
    case lookup_pt_None
    have "pt_sound (fmupd k p pt) g" unfolding pt_sound_def
    proof clarify
      fix x x' la gamma
      assume assm: "fmlookup (fmupd k p pt) (x', la) = Some (x, gamma)"
      show "x' = x \<and> (x, gamma) \<in> set (prods g) \<and> lookahead_for la x gamma g"
      proof (cases "k = (x', la)")
        case True
        then have "p = (x, gamma)" using assm by auto
        then show ?thesis using assms(1-4) Cons.prems(2) keys_are_lookaheads True by fastforce
      next
        case False
        then show ?thesis using Cons.prems(1) assm unfolding pt_sound_def by auto
      qed
    qed
    then show ?thesis using Cons.IH Cons.prems(2,3) lookup_pt_None by auto
  next
    case lookup_pt_Same
    then show ?thesis using Cons by auto
  qed
qed

lemma mkParseTable'_nested: "mkParseTable' suf nu fi fo (mkParseTable' pre nu fi fo pt)
  = mkParseTable' (pre @ suf) nu fi fo pt"
  by (induction pre arbitrary: pt) auto

lemma mkParseTable'_failure_preserved:
  "mkParseTable' pre nu fi fo pt = ERROR_GRAMMAR_NOT_LL1_AMB_LA e
  \<Longrightarrow> mkParseTable' (pre @ suf) nu fi fo pt = ERROR_GRAMMAR_NOT_LL1_AMB_LA e"
proof (induction suf arbitrary: pre)
  case Nil
  then show ?case by auto
next
  case (Cons p suf)
  have "mkParseTable' (pre @ [p]) nu fi fo pt
    = mkParseTable' [p] nu fi fo (mkParseTable' pre nu fi fo pt)"
    by (simp add: mkParseTable'_nested)
  then show ?case using Cons.IH[where pre = "pre @ [p]"] Cons.prems by
    (auto simp add: mkParseTable'_nested)
qed

lemma all_pre_pt_non_failure:
  "mkParseTable' (pre @ suf) nu fi fo (PT pt) = PT pt'
    \<Longrightarrow> \<exists>pre_pt'. mkParseTable' pre nu fi fo (PT pt) = PT pre_pt'"
  by (cases "mkParseTable' pre nu fi fo (PT pt)")
    (auto simp add: mkParseTable'_failure_preserved)

lemma mkParseTable'_preserves_soundness:
  assumes "nullable_set_for nu g" "first_map_for fi g" "follow_map_for fo g"
  shows "set ps \<subseteq> set (prods g) \<Longrightarrow> pt_sound pt g \<Longrightarrow> mkParseTable' ps nu fi fo (PT pt) = PT pt'
    \<Longrightarrow> pt_sound pt' g"
proof (induction ps arbitrary: pt)
  case Nil
  show ?case using Nil.prems(2,3) by auto
next
  case (Cons p ps)
  obtain pre_pt' where pre_pt'_def: "mkParseTable' [p] nu fi fo (PT pt) = PT pre_pt'"
    using all_pre_pt_non_failure[where pre = "[p]"] Cons.prems(3) by fastforce
  then have "pt_sound pre_pt' g" using assms Cons.prems pre_pt'_def by
    (auto intro: addEntries_preserves_soundness)
  then show ?case using Cons.IH Cons.prems(1,3) pre_pt'_def by auto
qed

lemma initial_pt_sound: "pt_sound fmempty g"
  unfolding pt_sound_def by simp

theorem mkParseTable_sound: "mkParseTable g = PT pt \<Longrightarrow> pt_sound pt g"
proof -
  assume assm: "mkParseTable g = PT pt"
  let ?nu = "mkNullableSet g"
  let ?fi = "mkFirstMap g ?nu"
  let ?fo = "mkFollowMap g ?nu ?fi"
  have "nullable_set_for ?nu g" by (rule mkNullableSet_correct)
  moreover have "first_map_for ?fi g" using calculation(1) by (rule mkFirstMap_correct)
  moreover have "follow_map_for ?fo g" using calculation(1,2) by - (rule mkFollowMap_correct)
  ultimately show "pt_sound pt g" by
    (metis assm initial_pt_sound mkParseTable'_preserves_soundness mkParseTable_def order_refl)
qed


subsection \<open>Completeness\<close>

lemma la_in_keysForProd:
  assumes "nullable_set_for nu g" "first_map_for fi g" "follow_map_for fo g"
    "lookahead_for la x gamma g"
  shows"(x, la) \<in> set (keysForProd nu fi fo (x, gamma))"
proof (cases "first_gamma g la gamma")
  case True
  then show ?thesis using assms(1,2) by
    (auto intro: first_gamma_firstGamma simp add: firstKeysForProd_def)
next
  case False
  have "nullableGamma gamma nu" using assms(1,4) False by
    (auto intro: nullable_gamma_nullableGamma simp add: lookahead_for_def)
  moreover have "la \<in> set (findOrEmpty x fo)" using assms(3,4) False by
    (auto simp add: lookahead_for_def follow_map_complete_def in_findOrEmpty_exists_set)
  ultimately show ?thesis by (simp add: followKeysForProd_def)
qed

lemma addEntries_lookup_same_or_none: "addEntries las xp (PT pt) = PT pt' \<Longrightarrow> fmlookup pt k = Some x
  \<Longrightarrow> fmlookup pt' k = Some x"
proof (induction las arbitrary: pt pt')
  case Nil
  then show ?case by auto
next
  case (Cons k' las)
  then show ?case by (cases "k' = k") (auto split: option.splits if_splits)
qed

lemma mkParseTable'_lookup_same_or_none: "mkParseTable' ps nu fi fo (PT pt) = PT pt'
  \<Longrightarrow> fmlookup pt k = Some x \<Longrightarrow> fmlookup pt' k = Some x"
proof (induction ps arbitrary: pt pt')
  case Nil
  then show ?case by auto
next
  case (Cons p ps)
  obtain pre_pt' where pre_pt'_def: "mkParseTable' [p] nu fi fo (PT pt) = PT pre_pt'"
    using Cons.prems(1) all_pre_pt_non_failure[where pre = "[p]"] by fastforce
  then have "fmlookup pre_pt' k = Some x" by
    (simp add: Cons.prems(2) addEntries_lookup_same_or_none)
  then show ?case using Cons.IH Cons.prems(1) pre_pt'_def by auto
qed

lemma addEntries_in_pt:
  "k \<in> set las \<Longrightarrow> addEntries las xp (PT pt) = PT pt' \<Longrightarrow> fmlookup pt' k = Some xp"
proof (induction las arbitrary: pt pt')
  case Nil
  then show ?case by auto
next
  case (Cons k' las)
  consider (is_k) "k = k'" | (in_las) "k \<in> set las" using Cons.prems(1) by auto
  then show ?case
  proof cases
    case is_k
    obtain pre_pt' where pre_pt'_def: "addEntries [k'] xp (PT pt) = PT pre_pt'" using Cons.prems(2)
      by (auto split: option.splits if_splits)
    then have "fmlookup pre_pt' k' = Some xp" by (auto split: option.splits if_splits)
    moreover have "addEntries las xp (PT pre_pt') = PT pt'" using Cons.prems(2) by
      (auto simp add: pre_pt'_def[symmetric] split: option.split)
    ultimately show ?thesis
      using addEntries_lookup_same_or_none[where pt = pre_pt'] pre_pt'_def is_k by auto
  next
    case in_las
    then show ?thesis using Cons.IH Cons.prems(2) by (auto split: option.splits if_splits)
  qed
qed

lemma mkParseTable'_complete': "nullable_set_for nu g \<Longrightarrow> first_map_for fi g
  \<Longrightarrow> follow_map_for fo g \<Longrightarrow> prods g = ppre @ psuf \<Longrightarrow> (x, gamma) \<in> set psuf
  \<Longrightarrow> lookahead_for la x gamma g \<Longrightarrow> mkParseTable' psuf nu fi fo (PT pt) = PT pt'
  \<Longrightarrow> fmlookup pt' (x, la) = Some (x, gamma)"
proof (induction psuf arbitrary: ppre pt)
  case Nil
  then show ?case by auto
next
  case (Cons p psuf)
  obtain x' gamma' where "p = (x', gamma')" by fastforce
  obtain pre_pt' where pre_pt'_def: "mkParseTable' [p] nu fi fo (PT pt) = PT pre_pt'"
    using Cons.prems(7) all_pre_pt_non_failure[where pre = "[p]"] by fastforce
  from Cons.prems(5) consider (in_psuf) "(x, gamma) \<in> set psuf" | (is_p) "p = (x, gamma)" by auto
  then show ?case
  proof cases
    case in_psuf
    then show ?thesis using Cons pre_pt'_def by auto
  next
    case is_p
    then have "(x, la) \<in> set (keysForProd nu fi fo p)" using Cons.prems(1-3,6) la_in_keysForProd by
      fastforce
    then have "fmlookup pre_pt' (x, la) = Some (x, gamma)"
      using addEntries_in_pt is_p pre_pt'_def by fastforce
    then show ?thesis using Cons.prems(7) mkParseTable'_lookup_same_or_none pre_pt'_def by fastforce
  qed
qed

lemma mkParseTable'_complete: "nullable_set_for nu g \<Longrightarrow> first_map_for fi g \<Longrightarrow> follow_map_for fo g
  \<Longrightarrow> (x, gamma) \<in> set (prods g) \<Longrightarrow> lookahead_for la x gamma g
  \<Longrightarrow> mkParseTable' (prods g) nu fi fo (PT fmempty) = PT pt
  \<Longrightarrow> fmlookup pt (x, la) = Some (x, gamma)"
  by (auto intro: mkParseTable'_complete'[where ?ppre = "[]"])

theorem mkParseTable_complete: "mkParseTable g = PT pt \<Longrightarrow> pt_complete pt g"
  unfolding pt_complete_def mkParseTable_def
  by (meson mkFirstMap_correct mkFollowMap_correct mkNullableSet_correct mkParseTable'_complete)

theorem mkParseTable_correct: "mkParseTable g = PT pt \<Longrightarrow> parse_table_correct pt g"
  by (auto simp add: mkParseTable_complete mkParseTable_sound)


end